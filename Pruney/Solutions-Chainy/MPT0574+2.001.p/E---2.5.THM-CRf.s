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
% DateTime   : Thu Dec  3 10:51:48 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 253 expanded)
%              Number of clauses        :   39 ( 117 expanded)
%              Number of leaves         :   12 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  103 ( 355 expanded)
%              Number of equality atoms :   35 ( 191 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t178_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_12,plain,(
    ! [X35,X36] : k3_tarski(k2_tarski(X35,X36)) = k2_xboole_0(X35,X36) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X33,X34] : k1_enumset1(X33,X33,X34) = k2_tarski(X33,X34) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X26,X27,X28] :
      ( ~ r1_tarski(X26,k2_xboole_0(X27,X28))
      | r1_tarski(k4_xboole_0(X26,X27),X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_15,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X29,X30] : r1_tarski(X29,k2_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_18,plain,(
    ! [X21,X22] :
      ( ( r1_tarski(X21,X22)
        | X21 != X22 )
      & ( r1_tarski(X22,X21)
        | X21 != X22 )
      & ( ~ r1_tarski(X21,X22)
        | ~ r1_tarski(X22,X21)
        | X21 = X22 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_19,plain,(
    ! [X23] : r1_tarski(k1_xboole_0,X23) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_20,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X24,X25] : k2_xboole_0(X24,k4_xboole_0(X25,X24)) = k2_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_21])).

fof(c_0_28,plain,(
    ! [X20] : k2_xboole_0(X20,X20) = X20 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t178_relat_1])).

cnf(c_0_34,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k4_xboole_0(X2,X1))) = k3_tarski(k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_21]),c_0_21])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_32,c_0_21])).

fof(c_0_37,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_38,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k10_relat_1(esk5_0,esk3_0),k10_relat_1(esk5_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

fof(c_0_39,plain,(
    ! [X37,X38,X39] :
      ( ~ v1_relat_1(X39)
      | k10_relat_1(X39,k2_xboole_0(X37,X38)) = k2_xboole_0(k10_relat_1(X39,X37),k10_relat_1(X39,X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

cnf(c_0_40,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

fof(c_0_41,plain,(
    ! [X31,X32] : k2_tarski(X31,X32) = k2_tarski(X32,X31) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_42,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk5_0,esk3_0),k10_relat_1(esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_27])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk1_2(k10_relat_1(esk5_0,esk3_0),k10_relat_1(esk5_0,esk4_0)),k10_relat_1(esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( k10_relat_1(X1,k3_tarski(k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_21]),c_0_21])).

cnf(c_0_52,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,esk4_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_16]),c_0_16])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk1_2(k10_relat_1(esk5_0,esk3_0),k10_relat_1(esk5_0,esk4_0)),k3_tarski(k1_enumset1(k10_relat_1(esk5_0,esk3_0),k10_relat_1(esk5_0,esk3_0),X1))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k3_tarski(k1_enumset1(k10_relat_1(esk5_0,X1),k10_relat_1(esk5_0,X1),k10_relat_1(esk5_0,X2))) = k10_relat_1(esk5_0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_53]),c_0_25])])).

cnf(c_0_58,plain,
    ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_40,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_2(k10_relat_1(esk5_0,esk3_0),k10_relat_1(esk5_0,esk4_0)),k10_relat_1(esk5_0,k3_tarski(k1_enumset1(esk3_0,esk3_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk3_0,esk3_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_57]),c_0_54]),c_0_58]),c_0_54])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk1_2(k10_relat_1(esk5_0,esk3_0),k10_relat_1(esk5_0,esk4_0)),k10_relat_1(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.47/0.69  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.47/0.69  # and selection function SelectNegativeLiterals.
% 0.47/0.69  #
% 0.47/0.69  # Preprocessing time       : 0.028 s
% 0.47/0.69  # Presaturation interreduction done
% 0.47/0.69  
% 0.47/0.69  # Proof found!
% 0.47/0.69  # SZS status Theorem
% 0.47/0.69  # SZS output start CNFRefutation
% 0.47/0.69  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.47/0.69  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.47/0.69  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.47/0.69  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.47/0.69  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.47/0.69  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.47/0.69  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.47/0.69  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.47/0.69  fof(t178_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 0.47/0.69  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.47/0.69  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 0.47/0.69  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.47/0.69  fof(c_0_12, plain, ![X35, X36]:k3_tarski(k2_tarski(X35,X36))=k2_xboole_0(X35,X36), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.47/0.69  fof(c_0_13, plain, ![X33, X34]:k1_enumset1(X33,X33,X34)=k2_tarski(X33,X34), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.47/0.69  fof(c_0_14, plain, ![X26, X27, X28]:(~r1_tarski(X26,k2_xboole_0(X27,X28))|r1_tarski(k4_xboole_0(X26,X27),X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.47/0.69  cnf(c_0_15, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.69  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.69  fof(c_0_17, plain, ![X29, X30]:r1_tarski(X29,k2_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.47/0.69  fof(c_0_18, plain, ![X21, X22]:(((r1_tarski(X21,X22)|X21!=X22)&(r1_tarski(X22,X21)|X21!=X22))&(~r1_tarski(X21,X22)|~r1_tarski(X22,X21)|X21=X22)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.47/0.69  fof(c_0_19, plain, ![X23]:r1_tarski(k1_xboole_0,X23), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.47/0.69  cnf(c_0_20, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.69  cnf(c_0_21, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.47/0.69  cnf(c_0_22, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.69  fof(c_0_23, plain, ![X24, X25]:k2_xboole_0(X24,k4_xboole_0(X25,X24))=k2_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.47/0.69  cnf(c_0_24, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.69  cnf(c_0_25, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.69  cnf(c_0_26, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.47/0.69  cnf(c_0_27, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_22, c_0_21])).
% 0.47/0.69  fof(c_0_28, plain, ![X20]:k2_xboole_0(X20,X20)=X20, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.47/0.69  cnf(c_0_29, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.47/0.69  cnf(c_0_30, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.47/0.69  cnf(c_0_31, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.47/0.69  cnf(c_0_32, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.47/0.69  fof(c_0_33, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t178_relat_1])).
% 0.47/0.69  cnf(c_0_34, plain, (k3_tarski(k1_enumset1(X1,X1,k4_xboole_0(X2,X1)))=k3_tarski(k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_21]), c_0_21])).
% 0.47/0.69  cnf(c_0_35, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.47/0.69  cnf(c_0_36, plain, (k3_tarski(k1_enumset1(X1,X1,X1))=X1), inference(rw,[status(thm)],[c_0_32, c_0_21])).
% 0.47/0.69  fof(c_0_37, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.47/0.69  fof(c_0_38, negated_conjecture, (v1_relat_1(esk5_0)&(r1_tarski(esk3_0,esk4_0)&~r1_tarski(k10_relat_1(esk5_0,esk3_0),k10_relat_1(esk5_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).
% 0.47/0.69  fof(c_0_39, plain, ![X37, X38, X39]:(~v1_relat_1(X39)|k10_relat_1(X39,k2_xboole_0(X37,X38))=k2_xboole_0(k10_relat_1(X39,X37),k10_relat_1(X39,X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 0.47/0.69  cnf(c_0_40, plain, (k3_tarski(k1_enumset1(X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.47/0.69  fof(c_0_41, plain, ![X31, X32]:k2_tarski(X31,X32)=k2_tarski(X32,X31), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.47/0.69  cnf(c_0_42, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.47/0.69  cnf(c_0_43, negated_conjecture, (~r1_tarski(k10_relat_1(esk5_0,esk3_0),k10_relat_1(esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.47/0.69  cnf(c_0_44, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.47/0.69  cnf(c_0_45, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.47/0.69  cnf(c_0_46, plain, (r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_40])).
% 0.47/0.69  cnf(c_0_47, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.47/0.69  cnf(c_0_48, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.47/0.69  cnf(c_0_49, plain, (r2_hidden(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_42, c_0_27])).
% 0.47/0.69  cnf(c_0_50, negated_conjecture, (r2_hidden(esk1_2(k10_relat_1(esk5_0,esk3_0),k10_relat_1(esk5_0,esk4_0)),k10_relat_1(esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.47/0.69  cnf(c_0_51, plain, (k10_relat_1(X1,k3_tarski(k1_enumset1(X2,X2,X3)))=k3_tarski(k1_enumset1(k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_21]), c_0_21])).
% 0.47/0.69  cnf(c_0_52, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.47/0.69  cnf(c_0_53, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,esk4_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.47/0.69  cnf(c_0_54, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_16]), c_0_16])).
% 0.47/0.69  cnf(c_0_55, negated_conjecture, (r2_hidden(esk1_2(k10_relat_1(esk5_0,esk3_0),k10_relat_1(esk5_0,esk4_0)),k3_tarski(k1_enumset1(k10_relat_1(esk5_0,esk3_0),k10_relat_1(esk5_0,esk3_0),X1)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.47/0.69  cnf(c_0_56, negated_conjecture, (k3_tarski(k1_enumset1(k10_relat_1(esk5_0,X1),k10_relat_1(esk5_0,X1),k10_relat_1(esk5_0,X2)))=k10_relat_1(esk5_0,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.47/0.69  cnf(c_0_57, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_53]), c_0_25])])).
% 0.47/0.69  cnf(c_0_58, plain, (k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_40, c_0_54])).
% 0.47/0.69  cnf(c_0_59, negated_conjecture, (r2_hidden(esk1_2(k10_relat_1(esk5_0,esk3_0),k10_relat_1(esk5_0,esk4_0)),k10_relat_1(esk5_0,k3_tarski(k1_enumset1(esk3_0,esk3_0,X1))))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.47/0.69  cnf(c_0_60, negated_conjecture, (k3_tarski(k1_enumset1(esk3_0,esk3_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_57]), c_0_54]), c_0_58]), c_0_54])).
% 0.47/0.69  cnf(c_0_61, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.47/0.69  cnf(c_0_62, negated_conjecture, (r2_hidden(esk1_2(k10_relat_1(esk5_0,esk3_0),k10_relat_1(esk5_0,esk4_0)),k10_relat_1(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.47/0.69  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_43]), ['proof']).
% 0.47/0.69  # SZS output end CNFRefutation
% 0.47/0.69  # Proof object total steps             : 64
% 0.47/0.69  # Proof object clause steps            : 39
% 0.47/0.69  # Proof object formula steps           : 25
% 0.47/0.69  # Proof object conjectures             : 15
% 0.47/0.69  # Proof object clause conjectures      : 12
% 0.47/0.69  # Proof object formula conjectures     : 3
% 0.47/0.69  # Proof object initial clauses used    : 16
% 0.47/0.69  # Proof object initial formulas used   : 12
% 0.47/0.69  # Proof object generating inferences   : 16
% 0.47/0.69  # Proof object simplifying inferences  : 17
% 0.47/0.69  # Training examples: 0 positive, 0 negative
% 0.47/0.69  # Parsed axioms                        : 13
% 0.47/0.69  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.69  # Initial clauses                      : 24
% 0.47/0.69  # Removed in clause preprocessing      : 2
% 0.47/0.69  # Initial clauses in saturation        : 22
% 0.47/0.69  # Processed clauses                    : 1643
% 0.47/0.69  # ...of these trivial                  : 79
% 0.47/0.69  # ...subsumed                          : 1133
% 0.47/0.69  # ...remaining for further processing  : 431
% 0.47/0.69  # Other redundant clauses eliminated   : 5
% 0.47/0.69  # Clauses deleted for lack of memory   : 0
% 0.47/0.69  # Backward-subsumed                    : 22
% 0.47/0.69  # Backward-rewritten                   : 65
% 0.47/0.69  # Generated clauses                    : 36500
% 0.47/0.69  # ...of the previous two non-trivial   : 27913
% 0.47/0.69  # Contextual simplify-reflections      : 4
% 0.47/0.69  # Paramodulations                      : 36493
% 0.47/0.69  # Factorizations                       : 2
% 0.47/0.69  # Equation resolutions                 : 5
% 0.47/0.69  # Propositional unsat checks           : 0
% 0.47/0.69  #    Propositional check models        : 0
% 0.47/0.69  #    Propositional check unsatisfiable : 0
% 0.47/0.69  #    Propositional clauses             : 0
% 0.47/0.69  #    Propositional clauses after purity: 0
% 0.47/0.69  #    Propositional unsat core size     : 0
% 0.47/0.69  #    Propositional preprocessing time  : 0.000
% 0.47/0.69  #    Propositional encoding time       : 0.000
% 0.47/0.69  #    Propositional solver time         : 0.000
% 0.47/0.69  #    Success case prop preproc time    : 0.000
% 0.47/0.69  #    Success case prop encoding time   : 0.000
% 0.47/0.69  #    Success case prop solver time     : 0.000
% 0.47/0.69  # Current number of processed clauses  : 318
% 0.47/0.69  #    Positive orientable unit clauses  : 70
% 0.47/0.69  #    Positive unorientable unit clauses: 1
% 0.47/0.69  #    Negative unit clauses             : 5
% 0.47/0.69  #    Non-unit-clauses                  : 242
% 0.47/0.69  # Current number of unprocessed clauses: 25897
% 0.47/0.69  # ...number of literals in the above   : 100466
% 0.47/0.69  # Current number of archived formulas  : 0
% 0.47/0.69  # Current number of archived clauses   : 110
% 0.47/0.69  # Clause-clause subsumption calls (NU) : 9556
% 0.47/0.69  # Rec. Clause-clause subsumption calls : 7023
% 0.47/0.69  # Non-unit clause-clause subsumptions  : 910
% 0.47/0.69  # Unit Clause-clause subsumption calls : 389
% 0.47/0.69  # Rewrite failures with RHS unbound    : 0
% 0.47/0.69  # BW rewrite match attempts            : 187
% 0.47/0.69  # BW rewrite match successes           : 45
% 0.47/0.69  # Condensation attempts                : 0
% 0.47/0.69  # Condensation successes               : 0
% 0.47/0.69  # Termbank termtop insertions          : 582743
% 0.47/0.70  
% 0.47/0.70  # -------------------------------------------------
% 0.47/0.70  # User time                : 0.340 s
% 0.47/0.70  # System time              : 0.012 s
% 0.47/0.70  # Total time               : 0.352 s
% 0.47/0.70  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
