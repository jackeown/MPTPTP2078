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
% DateTime   : Thu Dec  3 10:53:21 EST 2020

% Result     : Theorem 7.87s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :   49 (  98 expanded)
%              Number of clauses        :   30 (  43 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :  175 ( 302 expanded)
%              Number of equality atoms :   31 (  78 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(t74_relat_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).

fof(t38_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))
       => k1_funct_1(X3,X1) = k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(c_0_9,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(X27,k1_relat_1(X29))
        | ~ r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( X28 = k1_funct_1(X29,X27)
        | ~ r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( ~ r2_hidden(X27,k1_relat_1(X29))
        | X28 != k1_funct_1(X29,X27)
        | r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_10,plain,(
    ! [X20,X21,X22,X23] :
      ( ( r2_hidden(X20,X22)
        | ~ r2_hidden(k4_tarski(X20,X21),k5_relat_1(k6_relat_1(X22),X23))
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(k4_tarski(X20,X21),X23)
        | ~ r2_hidden(k4_tarski(X20,X21),k5_relat_1(k6_relat_1(X22),X23))
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(X20,X22)
        | ~ r2_hidden(k4_tarski(X20,X21),X23)
        | r2_hidden(k4_tarski(X20,X21),k5_relat_1(k6_relat_1(X22),X23))
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_relat_1])])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))
         => k1_funct_1(X3,X1) = k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t38_funct_1])).

cnf(c_0_12,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(X1,X3),k5_relat_1(k6_relat_1(X2),X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X24,X25] :
      ( ( v1_relat_1(k5_relat_1(X24,X25))
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( v1_funct_1(k5_relat_1(X24,X25))
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

fof(c_0_15,plain,(
    ! [X26] :
      ( v1_relat_1(k6_relat_1(X26))
      & v1_funct_1(k6_relat_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_16,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_17,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & r2_hidden(esk2_0,k3_xboole_0(k1_relat_1(esk4_0),esk3_0))
    & k1_funct_1(esk4_0,esk2_0) != k1_funct_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_19,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_20,plain,
    ( X1 = k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X4)
    | ~ v1_funct_1(k5_relat_1(k6_relat_1(X2),X3))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(X2),X3))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X4,X1),X3)
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_21,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_24,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | v1_relat_1(k5_relat_1(X18,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk2_0,k3_xboole_0(k1_relat_1(esk4_0),esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,plain,
    ( X1 = k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X4)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(X2),X3))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X4,X1),X3)
    | ~ r2_hidden(X4,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_31,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X4,k4_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk2_0,k4_xboole_0(k1_relat_1(esk4_0),k4_xboole_0(k1_relat_1(esk4_0),esk3_0))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_26]),c_0_26])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X2,k4_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_29,c_0_26])).

cnf(c_0_37,plain,
    ( X1 = k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X4)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X4,X1),X3)
    | ~ r2_hidden(X4,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_23])])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k1_relat_1(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(esk4_0,esk2_0) != k1_funct_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_43,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X3) = k1_funct_1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk2_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 7.87/8.11  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 7.87/8.11  # and selection function SelectComplexExceptUniqMaxHorn.
% 7.87/8.11  #
% 7.87/8.11  # Preprocessing time       : 0.028 s
% 7.87/8.11  # Presaturation interreduction done
% 7.87/8.11  
% 7.87/8.11  # Proof found!
% 7.87/8.11  # SZS status Theorem
% 7.87/8.11  # SZS output start CNFRefutation
% 7.87/8.11  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 7.87/8.11  fof(t74_relat_1, axiom, ![X1, X2, X3, X4]:(v1_relat_1(X4)=>(r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))<=>(r2_hidden(X1,X3)&r2_hidden(k4_tarski(X1,X2),X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_relat_1)).
% 7.87/8.11  fof(t38_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))=>k1_funct_1(X3,X1)=k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_1)).
% 7.87/8.11  fof(fc2_funct_1, axiom, ![X1, X2]:((((v1_relat_1(X1)&v1_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v1_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 7.87/8.11  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 7.87/8.11  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.87/8.11  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.87/8.11  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.87/8.11  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 7.87/8.11  fof(c_0_9, plain, ![X27, X28, X29]:(((r2_hidden(X27,k1_relat_1(X29))|~r2_hidden(k4_tarski(X27,X28),X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(X28=k1_funct_1(X29,X27)|~r2_hidden(k4_tarski(X27,X28),X29)|(~v1_relat_1(X29)|~v1_funct_1(X29))))&(~r2_hidden(X27,k1_relat_1(X29))|X28!=k1_funct_1(X29,X27)|r2_hidden(k4_tarski(X27,X28),X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 7.87/8.11  fof(c_0_10, plain, ![X20, X21, X22, X23]:(((r2_hidden(X20,X22)|~r2_hidden(k4_tarski(X20,X21),k5_relat_1(k6_relat_1(X22),X23))|~v1_relat_1(X23))&(r2_hidden(k4_tarski(X20,X21),X23)|~r2_hidden(k4_tarski(X20,X21),k5_relat_1(k6_relat_1(X22),X23))|~v1_relat_1(X23)))&(~r2_hidden(X20,X22)|~r2_hidden(k4_tarski(X20,X21),X23)|r2_hidden(k4_tarski(X20,X21),k5_relat_1(k6_relat_1(X22),X23))|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_relat_1])])])).
% 7.87/8.11  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k3_xboole_0(k1_relat_1(X3),X2))=>k1_funct_1(X3,X1)=k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X1)))), inference(assume_negation,[status(cth)],[t38_funct_1])).
% 7.87/8.11  cnf(c_0_12, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.87/8.11  cnf(c_0_13, plain, (r2_hidden(k4_tarski(X1,X3),k5_relat_1(k6_relat_1(X2),X4))|~r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),X4)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 7.87/8.11  fof(c_0_14, plain, ![X24, X25]:((v1_relat_1(k5_relat_1(X24,X25))|(~v1_relat_1(X24)|~v1_funct_1(X24)|~v1_relat_1(X25)|~v1_funct_1(X25)))&(v1_funct_1(k5_relat_1(X24,X25))|(~v1_relat_1(X24)|~v1_funct_1(X24)|~v1_relat_1(X25)|~v1_funct_1(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).
% 7.87/8.11  fof(c_0_15, plain, ![X26]:(v1_relat_1(k6_relat_1(X26))&v1_funct_1(k6_relat_1(X26))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 7.87/8.11  fof(c_0_16, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8))&(r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k3_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k3_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))&(r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 7.87/8.11  fof(c_0_17, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 7.87/8.11  fof(c_0_18, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(r2_hidden(esk2_0,k3_xboole_0(k1_relat_1(esk4_0),esk3_0))&k1_funct_1(esk4_0,esk2_0)!=k1_funct_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0),esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 7.87/8.11  fof(c_0_19, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 7.87/8.11  cnf(c_0_20, plain, (X1=k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X4)|~v1_funct_1(k5_relat_1(k6_relat_1(X2),X3))|~v1_relat_1(k5_relat_1(k6_relat_1(X2),X3))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X4,X1),X3)|~r2_hidden(X4,X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 7.87/8.11  cnf(c_0_21, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 7.87/8.11  cnf(c_0_22, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 7.87/8.11  cnf(c_0_23, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 7.87/8.11  fof(c_0_24, plain, ![X18, X19]:(~v1_relat_1(X18)|~v1_relat_1(X19)|v1_relat_1(k5_relat_1(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 7.87/8.11  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 7.87/8.11  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 7.87/8.11  cnf(c_0_27, negated_conjecture, (r2_hidden(esk2_0,k3_xboole_0(k1_relat_1(esk4_0),esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 7.87/8.11  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 7.87/8.11  cnf(c_0_29, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 7.87/8.11  cnf(c_0_30, plain, (X1=k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X4)|~v1_funct_1(X3)|~v1_relat_1(k5_relat_1(k6_relat_1(X2),X3))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X4,X1),X3)|~r2_hidden(X4,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])])).
% 7.87/8.11  cnf(c_0_31, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 7.87/8.11  cnf(c_0_32, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.87/8.11  cnf(c_0_33, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X4,k4_xboole_0(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 7.87/8.11  cnf(c_0_34, negated_conjecture, (r2_hidden(esk2_0,k4_xboole_0(k1_relat_1(esk4_0),k4_xboole_0(k1_relat_1(esk4_0),esk3_0)))), inference(rw,[status(thm)],[c_0_27, c_0_26])).
% 7.87/8.11  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_26]), c_0_26])).
% 7.87/8.11  cnf(c_0_36, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X2,k4_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_29, c_0_26])).
% 7.87/8.11  cnf(c_0_37, plain, (X1=k1_funct_1(k5_relat_1(k6_relat_1(X2),X3),X4)|~v1_funct_1(X3)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X4,X1),X3)|~r2_hidden(X4,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_23])])).
% 7.87/8.11  cnf(c_0_38, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_32])).
% 7.87/8.11  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(er,[status(thm)],[c_0_33])).
% 7.87/8.11  cnf(c_0_40, negated_conjecture, (r2_hidden(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k1_relat_1(esk4_0))))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 7.87/8.11  cnf(c_0_41, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_36])).
% 7.87/8.11  cnf(c_0_42, negated_conjecture, (k1_funct_1(esk4_0,esk2_0)!=k1_funct_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 7.87/8.11  cnf(c_0_43, plain, (k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X3)=k1_funct_1(X2,X3)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X3,k1_relat_1(X2))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 7.87/8.11  cnf(c_0_44, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 7.87/8.11  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 7.87/8.11  cnf(c_0_46, negated_conjecture, (r2_hidden(esk2_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 7.87/8.11  cnf(c_0_47, negated_conjecture, (r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_41, c_0_40])).
% 7.87/8.11  cnf(c_0_48, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])]), ['proof']).
% 7.87/8.11  # SZS output end CNFRefutation
% 7.87/8.11  # Proof object total steps             : 49
% 7.87/8.11  # Proof object clause steps            : 30
% 7.87/8.11  # Proof object formula steps           : 19
% 7.87/8.11  # Proof object conjectures             : 12
% 7.87/8.11  # Proof object clause conjectures      : 9
% 7.87/8.11  # Proof object formula conjectures     : 3
% 7.87/8.11  # Proof object initial clauses used    : 15
% 7.87/8.11  # Proof object initial formulas used   : 9
% 7.87/8.11  # Proof object generating inferences   : 7
% 7.87/8.11  # Proof object simplifying inferences  : 19
% 7.87/8.11  # Training examples: 0 positive, 0 negative
% 7.87/8.11  # Parsed axioms                        : 9
% 7.87/8.11  # Removed by relevancy pruning/SinE    : 0
% 7.87/8.11  # Initial clauses                      : 23
% 7.87/8.11  # Removed in clause preprocessing      : 1
% 7.87/8.11  # Initial clauses in saturation        : 22
% 7.87/8.11  # Processed clauses                    : 4847
% 7.87/8.11  # ...of these trivial                  : 6
% 7.87/8.11  # ...subsumed                          : 2621
% 7.87/8.11  # ...remaining for further processing  : 2220
% 7.87/8.11  # Other redundant clauses eliminated   : 675
% 7.87/8.11  # Clauses deleted for lack of memory   : 0
% 7.87/8.11  # Backward-subsumed                    : 71
% 7.87/8.11  # Backward-rewritten                   : 44
% 7.87/8.11  # Generated clauses                    : 627610
% 7.87/8.11  # ...of the previous two non-trivial   : 589682
% 7.87/8.11  # Contextual simplify-reflections      : 70
% 7.87/8.11  # Paramodulations                      : 626345
% 7.87/8.11  # Factorizations                       : 576
% 7.87/8.11  # Equation resolutions                 : 689
% 7.87/8.11  # Propositional unsat checks           : 0
% 7.87/8.11  #    Propositional check models        : 0
% 7.87/8.11  #    Propositional check unsatisfiable : 0
% 7.87/8.11  #    Propositional clauses             : 0
% 7.87/8.11  #    Propositional clauses after purity: 0
% 7.87/8.11  #    Propositional unsat core size     : 0
% 7.87/8.11  #    Propositional preprocessing time  : 0.000
% 7.87/8.11  #    Propositional encoding time       : 0.000
% 7.87/8.11  #    Propositional solver time         : 0.000
% 7.87/8.11  #    Success case prop preproc time    : 0.000
% 7.87/8.11  #    Success case prop encoding time   : 0.000
% 7.87/8.11  #    Success case prop solver time     : 0.000
% 7.87/8.11  # Current number of processed clauses  : 2080
% 7.87/8.11  #    Positive orientable unit clauses  : 11
% 7.87/8.11  #    Positive unorientable unit clauses: 1
% 7.87/8.11  #    Negative unit clauses             : 1
% 7.87/8.11  #    Non-unit-clauses                  : 2067
% 7.87/8.11  # Current number of unprocessed clauses: 584571
% 7.87/8.11  # ...number of literals in the above   : 3679176
% 7.87/8.11  # Current number of archived formulas  : 0
% 7.87/8.11  # Current number of archived clauses   : 137
% 7.87/8.11  # Clause-clause subsumption calls (NU) : 1231731
% 7.87/8.11  # Rec. Clause-clause subsumption calls : 180998
% 7.87/8.11  # Non-unit clause-clause subsumptions  : 2762
% 7.87/8.11  # Unit Clause-clause subsumption calls : 424
% 7.87/8.11  # Rewrite failures with RHS unbound    : 0
% 7.87/8.11  # BW rewrite match attempts            : 91
% 7.87/8.11  # BW rewrite match successes           : 14
% 7.87/8.11  # Condensation attempts                : 0
% 7.87/8.11  # Condensation successes               : 0
% 7.87/8.11  # Termbank termtop insertions          : 23552513
% 7.96/8.14  
% 7.96/8.14  # -------------------------------------------------
% 7.96/8.14  # User time                : 7.536 s
% 7.96/8.14  # System time              : 0.258 s
% 7.96/8.14  # Total time               : 7.795 s
% 7.96/8.14  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
