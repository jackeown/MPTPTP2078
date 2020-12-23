%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:47 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 236 expanded)
%              Number of clauses        :   48 ( 117 expanded)
%              Number of leaves         :    6 (  57 expanded)
%              Depth                    :   17
%              Number of atoms          :  157 ( 778 expanded)
%              Number of equality atoms :   43 ( 252 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t103_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X2),X1) = k7_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(c_0_6,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_7,plain,(
    ! [X22,X23] : k1_setfam_1(k2_tarski(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_tarski(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_11,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2))) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k7_relat_1(k7_relat_1(X3,X2),X1) = k7_relat_1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t103_relat_1])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X4)
    | X4 != k1_setfam_1(k2_tarski(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_9])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(k1_setfam_1(k2_tarski(X1,X2)),X3),X2)
    | r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & r1_tarski(esk3_0,esk4_0)
    & k7_relat_1(k7_relat_1(esk5_0,esk4_0),esk3_0) != k7_relat_1(esk5_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_20,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(k1_setfam_1(k2_tarski(X1,X2)),X3),X4)
    | r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X3)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r2_hidden(esk1_2(X1,k1_setfam_1(k2_tarski(X2,X3))),X3)
    | ~ r2_hidden(esk1_2(X1,k1_setfam_1(k2_tarski(X2,X3))),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_2(k1_setfam_1(k2_tarski(X1,esk3_0)),X2),esk4_0)
    | r1_tarski(k1_setfam_1(k2_tarski(X1,esk3_0)),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_9]),c_0_9])).

cnf(c_0_29,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,X2)))
    | ~ r2_hidden(esk1_2(k1_setfam_1(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_2(k1_setfam_1(k2_tarski(esk3_0,X1)),X2),esk4_0)
    | r1_tarski(k1_setfam_1(k2_tarski(esk3_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X4)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X4,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k2_tarski(esk3_0,X1)),k1_setfam_1(k2_tarski(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_35,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_9])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,k1_setfam_1(k2_tarski(esk4_0,X2)))
    | ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_38,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X26)
      | k7_relat_1(k7_relat_1(X26,X24),X25) = k7_relat_1(X26,k3_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_39,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_34,c_0_9])).

cnf(c_0_40,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(esk4_0,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,esk3_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_27])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_tarski(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_37,c_0_9])).

cnf(c_0_44,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_48,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_44,c_0_9])).

cnf(c_0_49,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,X1)) = X1
    | ~ r2_hidden(esk2_3(esk4_0,X1,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))) = k1_setfam_1(k2_tarski(X2,X3))
    | r2_hidden(esk2_3(X1,k1_setfam_1(k2_tarski(X2,X3)),k1_setfam_1(k2_tarski(X2,X3))),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_40])).

cnf(c_0_51,plain,
    ( k7_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3))) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_28])).

cnf(c_0_52,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,k1_setfam_1(k2_tarski(esk3_0,X1)))) = k1_setfam_1(k2_tarski(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_45,c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk5_0,esk4_0),esk3_0) != k7_relat_1(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_55,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_57,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk3_0,esk4_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_28])).

cnf(c_0_58,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk5_0,esk3_0),esk4_0) != k7_relat_1(esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_59,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk3_0),esk4_0) = k7_relat_1(X1,esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_56])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.62/0.81  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.62/0.81  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.62/0.81  #
% 0.62/0.81  # Preprocessing time       : 0.027 s
% 0.62/0.81  # Presaturation interreduction done
% 0.62/0.81  
% 0.62/0.81  # Proof found!
% 0.62/0.81  # SZS status Theorem
% 0.62/0.81  # SZS output start CNFRefutation
% 0.62/0.81  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.62/0.81  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.62/0.81  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.62/0.81  fof(t103_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X2),X1)=k7_relat_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 0.62/0.81  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.62/0.81  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 0.62/0.81  fof(c_0_6, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14))&(r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k3_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k3_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))&(r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.62/0.81  fof(c_0_7, plain, ![X22, X23]:k1_setfam_1(k2_tarski(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.62/0.81  cnf(c_0_8, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.62/0.81  cnf(c_0_9, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.62/0.81  cnf(c_0_10, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_tarski(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_8, c_0_9])).
% 0.62/0.81  fof(c_0_11, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.62/0.81  cnf(c_0_12, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.62/0.81  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2)))), inference(er,[status(thm)],[c_0_10])).
% 0.62/0.81  cnf(c_0_14, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.62/0.81  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X2),X1)=k7_relat_1(X3,X1)))), inference(assume_negation,[status(cth)],[t103_relat_1])).
% 0.62/0.81  cnf(c_0_16, plain, (r2_hidden(X1,X4)|X4!=k1_setfam_1(k2_tarski(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_12, c_0_9])).
% 0.62/0.81  cnf(c_0_17, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.62/0.81  cnf(c_0_18, plain, (r2_hidden(esk1_2(k1_setfam_1(k2_tarski(X1,X2)),X3),X2)|r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.62/0.81  fof(c_0_19, negated_conjecture, (v1_relat_1(esk5_0)&(r1_tarski(esk3_0,esk4_0)&k7_relat_1(k7_relat_1(esk5_0,esk4_0),esk3_0)!=k7_relat_1(esk5_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.62/0.81  fof(c_0_20, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.62/0.81  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.62/0.81  cnf(c_0_22, plain, (r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_16])).
% 0.62/0.81  cnf(c_0_23, plain, (r2_hidden(esk1_2(k1_setfam_1(k2_tarski(X1,X2)),X3),X4)|r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X3)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.62/0.81  cnf(c_0_24, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.62/0.81  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.62/0.81  cnf(c_0_26, plain, (r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))|~r2_hidden(esk1_2(X1,k1_setfam_1(k2_tarski(X2,X3))),X3)|~r2_hidden(esk1_2(X1,k1_setfam_1(k2_tarski(X2,X3))),X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.62/0.81  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_2(k1_setfam_1(k2_tarski(X1,esk3_0)),X2),esk4_0)|r1_tarski(k1_setfam_1(k2_tarski(X1,esk3_0)),X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.62/0.81  cnf(c_0_28, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_9]), c_0_9])).
% 0.62/0.81  cnf(c_0_29, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,X2)))|~r2_hidden(esk1_2(k1_setfam_1(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(X3,X2))),X3)), inference(spm,[status(thm)],[c_0_26, c_0_18])).
% 0.62/0.81  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_2(k1_setfam_1(k2_tarski(esk3_0,X1)),X2),esk4_0)|r1_tarski(k1_setfam_1(k2_tarski(esk3_0,X1)),X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.62/0.81  cnf(c_0_31, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.62/0.81  cnf(c_0_32, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,X4)|~r1_tarski(k1_setfam_1(k2_tarski(X4,X3)),X2)), inference(spm,[status(thm)],[c_0_17, c_0_22])).
% 0.62/0.81  cnf(c_0_33, negated_conjecture, (r1_tarski(k1_setfam_1(k2_tarski(esk3_0,X1)),k1_setfam_1(k2_tarski(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.62/0.81  cnf(c_0_34, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.62/0.81  cnf(c_0_35, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_31, c_0_9])).
% 0.62/0.81  cnf(c_0_36, negated_conjecture, (r2_hidden(X1,k1_setfam_1(k2_tarski(esk4_0,X2)))|~r2_hidden(X1,esk3_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.62/0.81  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.62/0.81  fof(c_0_38, plain, ![X24, X25, X26]:(~v1_relat_1(X26)|k7_relat_1(k7_relat_1(X26,X24),X25)=k7_relat_1(X26,k3_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.62/0.81  cnf(c_0_39, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_34, c_0_9])).
% 0.62/0.81  cnf(c_0_40, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_35])).
% 0.62/0.81  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,esk3_0)|~r2_hidden(X1,X3)|~r1_tarski(k1_setfam_1(k2_tarski(esk4_0,X3)),X2)), inference(spm,[status(thm)],[c_0_17, c_0_36])).
% 0.62/0.81  cnf(c_0_42, negated_conjecture, (r1_tarski(k1_setfam_1(k2_tarski(X1,esk3_0)),esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_27])).
% 0.62/0.81  cnf(c_0_43, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_tarski(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_37, c_0_9])).
% 0.62/0.81  cnf(c_0_44, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.62/0.81  cnf(c_0_45, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_40])).
% 0.62/0.81  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.62/0.81  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))), inference(er,[status(thm)],[c_0_43])).
% 0.62/0.81  cnf(c_0_48, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_44, c_0_9])).
% 0.62/0.81  cnf(c_0_49, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,X1))=X1|~r2_hidden(esk2_3(esk4_0,X1,X1),esk3_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.62/0.81  cnf(c_0_50, plain, (k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X3))))=k1_setfam_1(k2_tarski(X2,X3))|r2_hidden(esk2_3(X1,k1_setfam_1(k2_tarski(X2,X3)),k1_setfam_1(k2_tarski(X2,X3))),X2)), inference(spm,[status(thm)],[c_0_47, c_0_40])).
% 0.62/0.81  cnf(c_0_51, plain, (k7_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3)))=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_28])).
% 0.62/0.81  cnf(c_0_52, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,k1_setfam_1(k2_tarski(esk3_0,X1))))=k1_setfam_1(k2_tarski(esk3_0,X1))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.62/0.81  cnf(c_0_53, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(spm,[status(thm)],[c_0_45, c_0_40])).
% 0.62/0.81  cnf(c_0_54, negated_conjecture, (k7_relat_1(k7_relat_1(esk5_0,esk4_0),esk3_0)!=k7_relat_1(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.62/0.81  cnf(c_0_55, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_51])).
% 0.62/0.81  cnf(c_0_56, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.62/0.81  cnf(c_0_57, negated_conjecture, (k1_setfam_1(k2_tarski(esk3_0,esk4_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_28])).
% 0.62/0.81  cnf(c_0_58, negated_conjecture, (k7_relat_1(k7_relat_1(esk5_0,esk3_0),esk4_0)!=k7_relat_1(esk5_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.62/0.81  cnf(c_0_59, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk3_0),esk4_0)=k7_relat_1(X1,esk3_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_57])).
% 0.62/0.81  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_56])]), ['proof']).
% 0.62/0.81  # SZS output end CNFRefutation
% 0.62/0.81  # Proof object total steps             : 61
% 0.62/0.81  # Proof object clause steps            : 48
% 0.62/0.81  # Proof object formula steps           : 13
% 0.62/0.81  # Proof object conjectures             : 19
% 0.62/0.81  # Proof object clause conjectures      : 16
% 0.62/0.81  # Proof object formula conjectures     : 3
% 0.62/0.81  # Proof object initial clauses used    : 14
% 0.62/0.81  # Proof object initial formulas used   : 6
% 0.62/0.81  # Proof object generating inferences   : 24
% 0.62/0.81  # Proof object simplifying inferences  : 17
% 0.62/0.81  # Training examples: 0 positive, 0 negative
% 0.62/0.81  # Parsed axioms                        : 6
% 0.62/0.81  # Removed by relevancy pruning/SinE    : 0
% 0.62/0.81  # Initial clauses                      : 15
% 0.62/0.81  # Removed in clause preprocessing      : 1
% 0.62/0.81  # Initial clauses in saturation        : 14
% 0.62/0.81  # Processed clauses                    : 1499
% 0.62/0.81  # ...of these trivial                  : 40
% 0.62/0.81  # ...subsumed                          : 1031
% 0.62/0.81  # ...remaining for further processing  : 428
% 0.62/0.81  # Other redundant clauses eliminated   : 15
% 0.62/0.81  # Clauses deleted for lack of memory   : 0
% 0.62/0.81  # Backward-subsumed                    : 12
% 0.62/0.81  # Backward-rewritten                   : 67
% 0.62/0.81  # Generated clauses                    : 25955
% 0.62/0.81  # ...of the previous two non-trivial   : 24887
% 0.62/0.81  # Contextual simplify-reflections      : 2
% 0.62/0.81  # Paramodulations                      : 25634
% 0.62/0.81  # Factorizations                       : 306
% 0.62/0.81  # Equation resolutions                 : 15
% 0.62/0.81  # Propositional unsat checks           : 0
% 0.62/0.81  #    Propositional check models        : 0
% 0.62/0.81  #    Propositional check unsatisfiable : 0
% 0.62/0.81  #    Propositional clauses             : 0
% 0.62/0.81  #    Propositional clauses after purity: 0
% 0.62/0.81  #    Propositional unsat core size     : 0
% 0.62/0.81  #    Propositional preprocessing time  : 0.000
% 0.62/0.81  #    Propositional encoding time       : 0.000
% 0.62/0.81  #    Propositional solver time         : 0.000
% 0.62/0.81  #    Success case prop preproc time    : 0.000
% 0.62/0.81  #    Success case prop encoding time   : 0.000
% 0.62/0.81  #    Success case prop solver time     : 0.000
% 0.62/0.81  # Current number of processed clauses  : 332
% 0.62/0.81  #    Positive orientable unit clauses  : 26
% 0.62/0.81  #    Positive unorientable unit clauses: 1
% 0.62/0.81  #    Negative unit clauses             : 2
% 0.62/0.81  #    Non-unit-clauses                  : 303
% 0.62/0.81  # Current number of unprocessed clauses: 23299
% 0.62/0.81  # ...number of literals in the above   : 134757
% 0.62/0.81  # Current number of archived formulas  : 0
% 0.62/0.81  # Current number of archived clauses   : 94
% 0.62/0.81  # Clause-clause subsumption calls (NU) : 64680
% 0.62/0.81  # Rec. Clause-clause subsumption calls : 10375
% 0.62/0.81  # Non-unit clause-clause subsumptions  : 1044
% 0.62/0.81  # Unit Clause-clause subsumption calls : 950
% 0.62/0.81  # Rewrite failures with RHS unbound    : 0
% 0.62/0.81  # BW rewrite match attempts            : 219
% 0.62/0.81  # BW rewrite match successes           : 10
% 0.62/0.81  # Condensation attempts                : 0
% 0.62/0.81  # Condensation successes               : 0
% 0.62/0.81  # Termbank termtop insertions          : 652470
% 0.62/0.81  
% 0.62/0.81  # -------------------------------------------------
% 0.62/0.81  # User time                : 0.445 s
% 0.62/0.81  # System time              : 0.020 s
% 0.62/0.81  # Total time               : 0.465 s
% 0.62/0.81  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
