%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:21 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 114 expanded)
%              Number of clauses        :   32 (  51 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :  179 ( 318 expanded)
%              Number of equality atoms :   35 (  94 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(t74_relat_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t38_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))
       => k1_funct_1(X3,X1) = k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(c_0_10,plain,(
    ! [X29,X30,X31] :
      ( ( r2_hidden(X29,k1_relat_1(X31))
        | ~ r2_hidden(k4_tarski(X29,X30),X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( X30 = k1_funct_1(X31,X29)
        | ~ r2_hidden(k4_tarski(X29,X30),X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( ~ r2_hidden(X29,k1_relat_1(X31))
        | X30 != k1_funct_1(X31,X29)
        | r2_hidden(k4_tarski(X29,X30),X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_11,plain,(
    ! [X22,X23,X24,X25] :
      ( ( r2_hidden(X22,X24)
        | ~ r2_hidden(k4_tarski(X22,X23),k5_relat_1(k6_relat_1(X24),X25))
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(k4_tarski(X22,X23),X25)
        | ~ r2_hidden(k4_tarski(X22,X23),k5_relat_1(k6_relat_1(X24),X25))
        | ~ v1_relat_1(X25) )
      & ( ~ r2_hidden(X22,X24)
        | ~ r2_hidden(k4_tarski(X22,X23),X25)
        | r2_hidden(k4_tarski(X22,X23),k5_relat_1(k6_relat_1(X24),X25))
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_relat_1])])])).

fof(c_0_12,plain,(
    ! [X18,X19] : k1_setfam_1(k2_tarski(X18,X19)) = k3_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_13,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))
         => k1_funct_1(X3,X1) = k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t38_funct_1])).

cnf(c_0_15,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,X3),k5_relat_1(k6_relat_1(X2),X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X26,X27] :
      ( ( v1_relat_1(k5_relat_1(X26,X27))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( v1_funct_1(k5_relat_1(X26,X27))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

fof(c_0_18,plain,(
    ! [X28] :
      ( v1_relat_1(k6_relat_1(X28))
      & v1_funct_1(k6_relat_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_19,plain,(
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

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & r2_hidden(esk2_0,k3_xboole_0(k1_relat_1(esk4_0),esk3_0))
    & k1_funct_1(esk4_0,esk2_0) != k1_funct_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_23,plain,(
    ! [X14,X15] : k2_tarski(X14,X15) = k2_tarski(X15,X14) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_24,plain,
    ( X1 = k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X4)
    | ~ v1_funct_1(k5_relat_1(k6_relat_1(X2),X3))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(X2),X3))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X4,X1),X3)
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_25,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_28,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | v1_relat_1(k5_relat_1(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk2_0,k3_xboole_0(k1_relat_1(esk4_0),esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,plain,
    ( X1 = k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X4)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(X2),X3))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X4,X1),X3)
    | ~ r2_hidden(X4,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_35,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k1_enumset1(X4,X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk2_0,k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),esk3_0))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_39,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_21]),c_0_21])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k1_enumset1(X2,X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_33,c_0_30])).

cnf(c_0_41,plain,
    ( X1 = k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X4)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X4,X1),X3)
    | ~ r2_hidden(X4,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_27])])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk2_0,k1_setfam_1(k1_enumset1(esk3_0,esk3_0,k1_relat_1(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(esk4_0,esk2_0) != k1_funct_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_47,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X3) = k1_funct_1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_49,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk2_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:48:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.028 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.19/0.41  fof(t74_relat_1, axiom, ![X1, X2, X3, X4]:(v1_relat_1(X4)=>(r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))<=>(r2_hidden(X1,X3)&r2_hidden(k4_tarski(X1,X2),X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_relat_1)).
% 0.19/0.41  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.41  fof(t38_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))=>k1_funct_1(X3,X1)=k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_1)).
% 0.19/0.41  fof(fc2_funct_1, axiom, ![X1, X2]:((((v1_relat_1(X1)&v1_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v1_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 0.19/0.41  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.19/0.41  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.41  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.41  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.19/0.41  fof(c_0_10, plain, ![X29, X30, X31]:(((r2_hidden(X29,k1_relat_1(X31))|~r2_hidden(k4_tarski(X29,X30),X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(X30=k1_funct_1(X31,X29)|~r2_hidden(k4_tarski(X29,X30),X31)|(~v1_relat_1(X31)|~v1_funct_1(X31))))&(~r2_hidden(X29,k1_relat_1(X31))|X30!=k1_funct_1(X31,X29)|r2_hidden(k4_tarski(X29,X30),X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.19/0.41  fof(c_0_11, plain, ![X22, X23, X24, X25]:(((r2_hidden(X22,X24)|~r2_hidden(k4_tarski(X22,X23),k5_relat_1(k6_relat_1(X24),X25))|~v1_relat_1(X25))&(r2_hidden(k4_tarski(X22,X23),X25)|~r2_hidden(k4_tarski(X22,X23),k5_relat_1(k6_relat_1(X24),X25))|~v1_relat_1(X25)))&(~r2_hidden(X22,X24)|~r2_hidden(k4_tarski(X22,X23),X25)|r2_hidden(k4_tarski(X22,X23),k5_relat_1(k6_relat_1(X24),X25))|~v1_relat_1(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_relat_1])])])).
% 0.19/0.41  fof(c_0_12, plain, ![X18, X19]:k1_setfam_1(k2_tarski(X18,X19))=k3_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.41  fof(c_0_13, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.41  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))=>k1_funct_1(X3,X1)=k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X1)))), inference(assume_negation,[status(cth)],[t38_funct_1])).
% 0.19/0.41  cnf(c_0_15, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.41  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X1,X3),k5_relat_1(k6_relat_1(X2),X4))|~r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),X4)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  fof(c_0_17, plain, ![X26, X27]:((v1_relat_1(k5_relat_1(X26,X27))|(~v1_relat_1(X26)|~v1_funct_1(X26)|~v1_relat_1(X27)|~v1_funct_1(X27)))&(v1_funct_1(k5_relat_1(X26,X27))|(~v1_relat_1(X26)|~v1_funct_1(X26)|~v1_relat_1(X27)|~v1_funct_1(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).
% 0.19/0.41  fof(c_0_18, plain, ![X28]:(v1_relat_1(k6_relat_1(X28))&v1_funct_1(k6_relat_1(X28))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.19/0.41  fof(c_0_19, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.41  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  fof(c_0_22, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(r2_hidden(esk2_0,k3_xboole_0(k1_relat_1(esk4_0),esk3_0))&k1_funct_1(esk4_0,esk2_0)!=k1_funct_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0),esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.41  fof(c_0_23, plain, ![X14, X15]:k2_tarski(X14,X15)=k2_tarski(X15,X14), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.41  cnf(c_0_24, plain, (X1=k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X4)|~v1_funct_1(k5_relat_1(k6_relat_1(X2),X3))|~v1_relat_1(k5_relat_1(k6_relat_1(X2),X3))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X4,X1),X3)|~r2_hidden(X4,X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.41  cnf(c_0_25, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_26, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_27, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  fof(c_0_28, plain, ![X20, X21]:(~v1_relat_1(X20)|~v1_relat_1(X21)|v1_relat_1(k5_relat_1(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.19/0.41  cnf(c_0_29, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_30, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.41  cnf(c_0_31, negated_conjecture, (r2_hidden(esk2_0,k3_xboole_0(k1_relat_1(esk4_0),esk3_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_32, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.41  cnf(c_0_33, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_34, plain, (X1=k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X4)|~v1_funct_1(X3)|~v1_relat_1(k5_relat_1(k6_relat_1(X2),X3))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X4,X1),X3)|~r2_hidden(X4,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])])).
% 0.19/0.41  cnf(c_0_35, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_36, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.41  cnf(c_0_37, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k1_enumset1(X4,X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.41  cnf(c_0_38, negated_conjecture, (r2_hidden(esk2_0,k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),esk3_0)))), inference(rw,[status(thm)],[c_0_31, c_0_30])).
% 0.19/0.41  cnf(c_0_39, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_21]), c_0_21])).
% 0.19/0.41  cnf(c_0_40, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k1_enumset1(X2,X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_33, c_0_30])).
% 0.19/0.41  cnf(c_0_41, plain, (X1=k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X4)|~v1_funct_1(X3)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X4,X1),X3)|~r2_hidden(X4,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_27])])).
% 0.19/0.41  cnf(c_0_42, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k1_enumset1(X3,X3,X2)))), inference(er,[status(thm)],[c_0_37])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (r2_hidden(esk2_0,k1_setfam_1(k1_enumset1(esk3_0,esk3_0,k1_relat_1(esk4_0))))), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.41  cnf(c_0_45, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))), inference(er,[status(thm)],[c_0_40])).
% 0.19/0.41  cnf(c_0_46, negated_conjecture, (k1_funct_1(esk4_0,esk2_0)!=k1_funct_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_47, plain, (k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X3)=k1_funct_1(X2,X3)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X3,k1_relat_1(X2))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.41  cnf(c_0_48, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_49, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_50, negated_conjecture, (r2_hidden(esk2_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_45, c_0_44])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_51])]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 53
% 0.19/0.41  # Proof object clause steps            : 32
% 0.19/0.41  # Proof object formula steps           : 21
% 0.19/0.41  # Proof object conjectures             : 12
% 0.19/0.41  # Proof object clause conjectures      : 9
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 16
% 0.19/0.41  # Proof object initial formulas used   : 10
% 0.19/0.41  # Proof object generating inferences   : 7
% 0.19/0.41  # Proof object simplifying inferences  : 20
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 10
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 24
% 0.19/0.41  # Removed in clause preprocessing      : 2
% 0.19/0.41  # Initial clauses in saturation        : 22
% 0.19/0.41  # Processed clauses                    : 165
% 0.19/0.41  # ...of these trivial                  : 0
% 0.19/0.41  # ...subsumed                          : 52
% 0.19/0.41  # ...remaining for further processing  : 113
% 0.19/0.41  # Other redundant clauses eliminated   : 4
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 2
% 0.19/0.41  # Backward-rewritten                   : 1
% 0.19/0.41  # Generated clauses                    : 1489
% 0.19/0.41  # ...of the previous two non-trivial   : 1401
% 0.19/0.41  # Contextual simplify-reflections      : 3
% 0.19/0.41  # Paramodulations                      : 1469
% 0.19/0.41  # Factorizations                       : 16
% 0.19/0.41  # Equation resolutions                 : 4
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
% 0.19/0.41  # Current number of processed clauses  : 85
% 0.19/0.41  #    Positive orientable unit clauses  : 8
% 0.19/0.41  #    Positive unorientable unit clauses: 1
% 0.19/0.41  #    Negative unit clauses             : 1
% 0.19/0.41  #    Non-unit-clauses                  : 75
% 0.19/0.41  # Current number of unprocessed clauses: 1278
% 0.19/0.41  # ...number of literals in the above   : 6200
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 26
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 1451
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 759
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 57
% 0.19/0.41  # Unit Clause-clause subsumption calls : 9
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 12
% 0.19/0.41  # BW rewrite match successes           : 8
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 33439
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.064 s
% 0.19/0.41  # System time              : 0.004 s
% 0.19/0.41  # Total time               : 0.068 s
% 0.19/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
