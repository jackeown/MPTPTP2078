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
% DateTime   : Thu Dec  3 10:47:17 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 763 expanded)
%              Number of clauses        :   40 ( 364 expanded)
%              Number of leaves         :   11 ( 196 expanded)
%              Depth                    :   12
%              Number of atoms          :  130 (1359 expanded)
%              Number of equality atoms :   73 ( 818 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t10_setfam_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(X1,X2)) != k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(t11_setfam_1,axiom,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t12_setfam_1,conjecture,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t18_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(c_0_11,plain,(
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

fof(c_0_12,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k4_xboole_0(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X17,X18,X20,X21,X22] :
      ( ( r1_xboole_0(X17,X18)
        | r2_hidden(esk2_2(X17,X18),k3_xboole_0(X17,X18)) )
      & ( ~ r2_hidden(X22,k3_xboole_0(X20,X21))
        | ~ r1_xboole_0(X20,X21) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_14,plain,(
    ! [X16] : k3_xboole_0(X16,X16) = X16 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_15,plain,(
    ! [X14,X15] :
      ( ( ~ r1_xboole_0(X14,X15)
        | k3_xboole_0(X14,X15) = k1_xboole_0 )
      & ( k3_xboole_0(X14,X15) != k1_xboole_0
        | r1_xboole_0(X14,X15) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X30,X31] :
      ( X30 = k1_xboole_0
      | X31 = k1_xboole_0
      | k1_setfam_1(k2_xboole_0(X30,X31)) = k3_xboole_0(k1_setfam_1(X30),k1_setfam_1(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).

fof(c_0_19,plain,(
    ! [X32] : k1_setfam_1(k1_tarski(X32)) = X32 ),
    inference(variable_rename,[status(thm)],[t11_setfam_1])).

fof(c_0_20,plain,(
    ! [X27] : k2_tarski(X27,X27) = k1_tarski(X27) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X2,k4_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t12_setfam_1])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k1_setfam_1(k2_xboole_0(X1,X2)) = k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
    ! [X25,X26] : k2_tarski(X25,X26) = k2_xboole_0(k1_tarski(X25),k1_tarski(X26)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_31,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_17])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_17])).

fof(c_0_36,negated_conjecture,(
    k1_setfam_1(k2_tarski(esk3_0,esk4_0)) != k3_xboole_0(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

cnf(c_0_37,plain,
    ( X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k1_setfam_1(k2_xboole_0(X1,X2)) = k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_17])).

cnf(c_0_38,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,plain,
    ( ~ r1_xboole_0(X1,X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_32])])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_44,plain,(
    ! [X28,X29] :
      ( k3_xboole_0(k1_tarski(X28),k1_tarski(X29)) != k1_tarski(X28)
      | X28 = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_zfmisc_1])])).

cnf(c_0_45,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk3_0,esk4_0)) != k3_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),X2)) = k1_setfam_1(k2_xboole_0(X1,k2_tarski(X2,X2)))
    | k2_tarski(X2,X2) = k1_xboole_0
    | X1 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_29]),c_0_29])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_17])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | r2_hidden(esk2_2(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_43])).

cnf(c_0_51,plain,
    ( X1 = X2
    | k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk3_0,esk4_0)) != k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_17])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_tarski(X1,X2))
    | k2_tarski(X1,X1) = k1_xboole_0
    | k2_tarski(X2,X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_38]),c_0_38])).

cnf(c_0_54,plain,
    ( k1_xboole_0 = X1
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_48])).

cnf(c_0_55,plain,
    ( r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( X1 = X2
    | k4_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))) != k2_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_29]),c_0_29]),c_0_29]),c_0_17])).

cnf(c_0_57,negated_conjecture,
    ( k2_tarski(esk4_0,esk4_0) = k1_xboole_0
    | k2_tarski(esk3_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( k2_tarski(esk3_0,esk3_0) = k1_xboole_0
    | esk4_0 = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_60,negated_conjecture,
    ( k2_tarski(esk3_0,esk3_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_59]),c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( esk3_0 = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_60]),c_0_58])])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_61]),c_0_61])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.27/2.52  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 2.27/2.52  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.27/2.52  #
% 2.27/2.52  # Preprocessing time       : 0.027 s
% 2.27/2.52  # Presaturation interreduction done
% 2.27/2.52  
% 2.27/2.52  # Proof found!
% 2.27/2.52  # SZS status Theorem
% 2.27/2.52  # SZS output start CNFRefutation
% 2.27/2.52  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.27/2.52  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.27/2.52  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.27/2.52  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.27/2.52  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.27/2.52  fof(t10_setfam_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&k1_setfam_1(k2_xboole_0(X1,X2))!=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.27/2.52  fof(t11_setfam_1, axiom, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.27/2.52  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.27/2.52  fof(t12_setfam_1, conjecture, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.27/2.52  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.27/2.52  fof(t18_zfmisc_1, axiom, ![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 2.27/2.52  fof(c_0_11, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 2.27/2.52  fof(c_0_12, plain, ![X23, X24]:k4_xboole_0(X23,k4_xboole_0(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.27/2.52  fof(c_0_13, plain, ![X17, X18, X20, X21, X22]:((r1_xboole_0(X17,X18)|r2_hidden(esk2_2(X17,X18),k3_xboole_0(X17,X18)))&(~r2_hidden(X22,k3_xboole_0(X20,X21))|~r1_xboole_0(X20,X21))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 2.27/2.52  fof(c_0_14, plain, ![X16]:k3_xboole_0(X16,X16)=X16, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 2.27/2.52  fof(c_0_15, plain, ![X14, X15]:((~r1_xboole_0(X14,X15)|k3_xboole_0(X14,X15)=k1_xboole_0)&(k3_xboole_0(X14,X15)!=k1_xboole_0|r1_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 2.27/2.52  cnf(c_0_16, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.27/2.52  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.27/2.52  fof(c_0_18, plain, ![X30, X31]:(X30=k1_xboole_0|X31=k1_xboole_0|k1_setfam_1(k2_xboole_0(X30,X31))=k3_xboole_0(k1_setfam_1(X30),k1_setfam_1(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).
% 2.27/2.52  fof(c_0_19, plain, ![X32]:k1_setfam_1(k1_tarski(X32))=X32, inference(variable_rename,[status(thm)],[t11_setfam_1])).
% 2.27/2.52  fof(c_0_20, plain, ![X27]:k2_tarski(X27,X27)=k1_tarski(X27), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 2.27/2.52  cnf(c_0_21, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.27/2.52  cnf(c_0_22, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.27/2.52  cnf(c_0_23, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.27/2.52  cnf(c_0_24, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X2,k4_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 2.27/2.52  cnf(c_0_25, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.27/2.52  fof(c_0_26, negated_conjecture, ~(![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(assume_negation,[status(cth)],[t12_setfam_1])).
% 2.27/2.52  cnf(c_0_27, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k1_setfam_1(k2_xboole_0(X1,X2))=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.27/2.52  cnf(c_0_28, plain, (k1_setfam_1(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.27/2.52  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.27/2.52  fof(c_0_30, plain, ![X25, X26]:k2_tarski(X25,X26)=k2_xboole_0(k1_tarski(X25),k1_tarski(X26)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 2.27/2.52  cnf(c_0_31, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_21, c_0_17])).
% 2.27/2.52  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_22, c_0_17])).
% 2.27/2.52  cnf(c_0_33, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_23, c_0_17])).
% 2.27/2.52  cnf(c_0_34, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_24])).
% 2.27/2.52  cnf(c_0_35, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_25, c_0_17])).
% 2.27/2.52  fof(c_0_36, negated_conjecture, k1_setfam_1(k2_tarski(esk3_0,esk4_0))!=k3_xboole_0(esk3_0,esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 2.27/2.52  cnf(c_0_37, plain, (X2=k1_xboole_0|X1=k1_xboole_0|k1_setfam_1(k2_xboole_0(X1,X2))=k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)))), inference(rw,[status(thm)],[c_0_27, c_0_17])).
% 2.27/2.52  cnf(c_0_38, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 2.27/2.52  cnf(c_0_39, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.27/2.52  cnf(c_0_40, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.27/2.52  cnf(c_0_41, plain, (~r1_xboole_0(X1,X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 2.27/2.52  cnf(c_0_42, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_32])])).
% 2.27/2.52  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 2.27/2.52  fof(c_0_44, plain, ![X28, X29]:(k3_xboole_0(k1_tarski(X28),k1_tarski(X29))!=k1_tarski(X28)|X28=X29), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_zfmisc_1])])).
% 2.27/2.52  cnf(c_0_45, negated_conjecture, (k1_setfam_1(k2_tarski(esk3_0,esk4_0))!=k3_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.27/2.52  cnf(c_0_46, plain, (k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),X2))=k1_setfam_1(k2_xboole_0(X1,k2_tarski(X2,X2)))|k2_tarski(X2,X2)=k1_xboole_0|X1=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 2.27/2.52  cnf(c_0_47, plain, (k2_tarski(X1,X2)=k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_29]), c_0_29])).
% 2.27/2.52  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_40, c_0_17])).
% 2.27/2.52  cnf(c_0_49, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 2.27/2.52  cnf(c_0_50, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|r2_hidden(esk2_2(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X1)), inference(spm,[status(thm)],[c_0_34, c_0_43])).
% 2.27/2.52  cnf(c_0_51, plain, (X1=X2|k3_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 2.27/2.52  cnf(c_0_52, negated_conjecture, (k1_setfam_1(k2_tarski(esk3_0,esk4_0))!=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_45, c_0_17])).
% 2.27/2.52  cnf(c_0_53, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_tarski(X1,X2))|k2_tarski(X1,X1)=k1_xboole_0|k2_tarski(X2,X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_38]), c_0_38])).
% 2.27/2.52  cnf(c_0_54, plain, (k1_xboole_0=X1|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_32, c_0_48])).
% 2.27/2.52  cnf(c_0_55, plain, (r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 2.27/2.52  cnf(c_0_56, plain, (X1=X2|k4_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)))!=k2_tarski(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_29]), c_0_29]), c_0_29]), c_0_17])).
% 2.27/2.52  cnf(c_0_57, negated_conjecture, (k2_tarski(esk4_0,esk4_0)=k1_xboole_0|k2_tarski(esk3_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 2.27/2.52  cnf(c_0_58, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 2.27/2.52  cnf(c_0_59, negated_conjecture, (k2_tarski(esk3_0,esk3_0)=k1_xboole_0|esk4_0=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 2.27/2.52  cnf(c_0_60, negated_conjecture, (k2_tarski(esk3_0,esk3_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_59]), c_0_59])).
% 2.27/2.52  cnf(c_0_61, negated_conjecture, (esk3_0=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_60]), c_0_58])])).
% 2.27/2.52  cnf(c_0_62, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_61]), c_0_61])]), ['proof']).
% 2.27/2.52  # SZS output end CNFRefutation
% 2.27/2.52  # Proof object total steps             : 63
% 2.27/2.52  # Proof object clause steps            : 40
% 2.27/2.52  # Proof object formula steps           : 23
% 2.27/2.52  # Proof object conjectures             : 10
% 2.27/2.52  # Proof object clause conjectures      : 7
% 2.27/2.52  # Proof object formula conjectures     : 3
% 2.27/2.52  # Proof object initial clauses used    : 13
% 2.27/2.52  # Proof object initial formulas used   : 11
% 2.27/2.52  # Proof object generating inferences   : 14
% 2.27/2.52  # Proof object simplifying inferences  : 27
% 2.27/2.52  # Training examples: 0 positive, 0 negative
% 2.27/2.52  # Parsed axioms                        : 11
% 2.27/2.52  # Removed by relevancy pruning/SinE    : 0
% 2.27/2.52  # Initial clauses                      : 18
% 2.27/2.52  # Removed in clause preprocessing      : 2
% 2.27/2.52  # Initial clauses in saturation        : 16
% 2.27/2.52  # Processed clauses                    : 5364
% 2.27/2.52  # ...of these trivial                  : 14
% 2.27/2.52  # ...subsumed                          : 4502
% 2.27/2.52  # ...remaining for further processing  : 848
% 2.27/2.52  # Other redundant clauses eliminated   : 3463
% 2.27/2.52  # Clauses deleted for lack of memory   : 0
% 2.27/2.52  # Backward-subsumed                    : 58
% 2.27/2.52  # Backward-rewritten                   : 762
% 2.27/2.52  # Generated clauses                    : 178399
% 2.27/2.52  # ...of the previous two non-trivial   : 169042
% 2.27/2.52  # Contextual simplify-reflections      : 29
% 2.27/2.52  # Paramodulations                      : 174704
% 2.27/2.52  # Factorizations                       : 232
% 2.27/2.52  # Equation resolutions                 : 3463
% 2.27/2.52  # Propositional unsat checks           : 0
% 2.27/2.52  #    Propositional check models        : 0
% 2.27/2.52  #    Propositional check unsatisfiable : 0
% 2.27/2.52  #    Propositional clauses             : 0
% 2.27/2.52  #    Propositional clauses after purity: 0
% 2.27/2.52  #    Propositional unsat core size     : 0
% 2.27/2.52  #    Propositional preprocessing time  : 0.000
% 2.27/2.52  #    Propositional encoding time       : 0.000
% 2.27/2.52  #    Propositional solver time         : 0.000
% 2.27/2.52  #    Success case prop preproc time    : 0.000
% 2.27/2.52  #    Success case prop encoding time   : 0.000
% 2.27/2.52  #    Success case prop solver time     : 0.000
% 2.27/2.52  # Current number of processed clauses  : 9
% 2.27/2.52  #    Positive orientable unit clauses  : 2
% 2.27/2.52  #    Positive unorientable unit clauses: 1
% 2.27/2.52  #    Negative unit clauses             : 1
% 2.27/2.52  #    Non-unit-clauses                  : 5
% 2.27/2.52  # Current number of unprocessed clauses: 162722
% 2.27/2.52  # ...number of literals in the above   : 1048407
% 2.27/2.52  # Current number of archived formulas  : 0
% 2.27/2.52  # Current number of archived clauses   : 838
% 2.27/2.52  # Clause-clause subsumption calls (NU) : 80483
% 2.27/2.52  # Rec. Clause-clause subsumption calls : 34221
% 2.27/2.52  # Non-unit clause-clause subsumptions  : 2677
% 2.27/2.52  # Unit Clause-clause subsumption calls : 113
% 2.27/2.52  # Rewrite failures with RHS unbound    : 3
% 2.27/2.52  # BW rewrite match attempts            : 436
% 2.27/2.52  # BW rewrite match successes           : 429
% 2.27/2.52  # Condensation attempts                : 0
% 2.27/2.52  # Condensation successes               : 0
% 2.27/2.52  # Termbank termtop insertions          : 4785198
% 2.27/2.53  
% 2.27/2.53  # -------------------------------------------------
% 2.27/2.53  # User time                : 2.110 s
% 2.27/2.53  # System time              : 0.066 s
% 2.27/2.53  # Total time               : 2.177 s
% 2.27/2.53  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
