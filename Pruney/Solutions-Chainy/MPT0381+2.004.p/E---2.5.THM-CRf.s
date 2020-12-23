%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:54 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   56 (  87 expanded)
%              Number of clauses        :   27 (  36 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :  124 ( 161 expanded)
%              Number of equality atoms :   28 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t63_subset_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t55_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ( X1 != k1_xboole_0
       => m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_14,plain,(
    ! [X33,X34,X35] :
      ( ( r2_hidden(X33,X34)
        | ~ r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))) )
      & ( X33 != X35
        | ~ r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))) )
      & ( ~ r2_hidden(X33,X34)
        | X33 = X35
        | r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_15,plain,(
    ! [X23] : k2_tarski(X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X20,X21] : k4_xboole_0(X20,X21) = k5_xboole_0(X20,k3_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,plain,(
    ! [X26,X27,X28] : k2_enumset1(X26,X26,X27,X28) = k1_enumset1(X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X29,X30,X31,X32] : k3_enumset1(X29,X29,X30,X31,X32) = k2_enumset1(X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    inference(assume_negation,[status(cth)],[t63_subset_1])).

fof(c_0_21,plain,(
    ! [X36,X37] :
      ( ( ~ m1_subset_1(X37,X36)
        | r2_hidden(X37,X36)
        | v1_xboole_0(X36) )
      & ( ~ r2_hidden(X37,X36)
        | m1_subset_1(X37,X36)
        | v1_xboole_0(X36) )
      & ( ~ m1_subset_1(X37,X36)
        | v1_xboole_0(X37)
        | ~ v1_xboole_0(X36) )
      & ( ~ v1_xboole_0(X37)
        | m1_subset_1(X37,X36)
        | ~ v1_xboole_0(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_22,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_23,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X11,X12,X13] :
      ( ( ~ r2_hidden(X11,X12)
        | ~ r2_hidden(X11,X13)
        | ~ r2_hidden(X11,k5_xboole_0(X12,X13)) )
      & ( r2_hidden(X11,X12)
        | r2_hidden(X11,X13)
        | ~ r2_hidden(X11,k5_xboole_0(X12,X13)) )
      & ( ~ r2_hidden(X11,X12)
        | r2_hidden(X11,X13)
        | r2_hidden(X11,k5_xboole_0(X12,X13)) )
      & ( ~ r2_hidden(X11,X13)
        | r2_hidden(X11,X12)
        | r2_hidden(X11,k5_xboole_0(X12,X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

fof(c_0_30,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    & ~ m1_subset_1(k1_tarski(esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_31,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X39,X38)
      | X38 = k1_xboole_0
      | m1_subset_1(k1_tarski(X39),k1_zfmisc_1(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_subset_1])])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_34,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r1_xboole_0(X14,X15)
        | r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X19,k3_xboole_0(X17,X18))
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_35,plain,(
    ! [X22] : r1_xboole_0(X22,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_36,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k5_xboole_0(X3,k3_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( X2 = k1_xboole_0
    | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( ~ m1_subset_1(k1_tarski(esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_44,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)))) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk3_0,k5_xboole_0(esk4_0,X1))
    | r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( X2 = k1_xboole_0
    | m1_subset_1(k3_enumset1(X1,X1,X1,X1,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_24]),c_0_25]),c_0_27]),c_0_28])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( ~ m1_subset_1(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_24]),c_0_25]),c_0_27]),c_0_28])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk3_0,k3_xboole_0(esk4_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:08:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.13/0.38  # and selection function SelectNegativeLiterals.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.38  fof(t63_subset_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.13/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.13/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.38  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.13/0.38  fof(t55_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 0.13/0.38  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.13/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.13/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.38  fof(c_0_14, plain, ![X33, X34, X35]:(((r2_hidden(X33,X34)|~r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))))&(X33!=X35|~r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35)))))&(~r2_hidden(X33,X34)|X33=X35|r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.13/0.38  fof(c_0_15, plain, ![X23]:k2_tarski(X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_16, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_17, plain, ![X20, X21]:k4_xboole_0(X20,X21)=k5_xboole_0(X20,k3_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.38  fof(c_0_18, plain, ![X26, X27, X28]:k2_enumset1(X26,X26,X27,X28)=k1_enumset1(X26,X27,X28), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_19, plain, ![X29, X30, X31, X32]:k3_enumset1(X29,X29,X30,X31,X32)=k2_enumset1(X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.38  fof(c_0_20, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)))), inference(assume_negation,[status(cth)],[t63_subset_1])).
% 0.13/0.38  fof(c_0_21, plain, ![X36, X37]:(((~m1_subset_1(X37,X36)|r2_hidden(X37,X36)|v1_xboole_0(X36))&(~r2_hidden(X37,X36)|m1_subset_1(X37,X36)|v1_xboole_0(X36)))&((~m1_subset_1(X37,X36)|v1_xboole_0(X37)|~v1_xboole_0(X36))&(~v1_xboole_0(X37)|m1_subset_1(X37,X36)|~v1_xboole_0(X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.13/0.38  fof(c_0_22, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.38  cnf(c_0_23, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_28, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  fof(c_0_29, plain, ![X11, X12, X13]:(((~r2_hidden(X11,X12)|~r2_hidden(X11,X13)|~r2_hidden(X11,k5_xboole_0(X12,X13)))&(r2_hidden(X11,X12)|r2_hidden(X11,X13)|~r2_hidden(X11,k5_xboole_0(X12,X13))))&((~r2_hidden(X11,X12)|r2_hidden(X11,X13)|r2_hidden(X11,k5_xboole_0(X12,X13)))&(~r2_hidden(X11,X13)|r2_hidden(X11,X12)|r2_hidden(X11,k5_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.13/0.38  fof(c_0_30, negated_conjecture, (r2_hidden(esk3_0,esk4_0)&~m1_subset_1(k1_tarski(esk3_0),k1_zfmisc_1(esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.13/0.38  fof(c_0_31, plain, ![X38, X39]:(~m1_subset_1(X39,X38)|(X38=k1_xboole_0|m1_subset_1(k1_tarski(X39),k1_zfmisc_1(X38)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_subset_1])])).
% 0.13/0.38  cnf(c_0_32, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_33, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  fof(c_0_34, plain, ![X14, X15, X17, X18, X19]:((r1_xboole_0(X14,X15)|r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)))&(~r2_hidden(X19,k3_xboole_0(X17,X18))|~r1_xboole_0(X17,X18))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.13/0.38  fof(c_0_35, plain, ![X22]:r1_xboole_0(X22,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.13/0.38  cnf(c_0_36, plain, (X1!=X2|~r2_hidden(X1,k5_xboole_0(X3,k3_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 0.13/0.38  cnf(c_0_37, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_39, plain, (X2=k1_xboole_0|m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_40, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (~m1_subset_1(k1_tarski(esk3_0),k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_42, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_43, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  fof(c_0_44, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.38  cnf(c_0_45, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1))))), inference(er,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(esk3_0,k5_xboole_0(esk4_0,X1))|r2_hidden(esk3_0,X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.38  cnf(c_0_47, plain, (X2=k1_xboole_0|m1_subset_1(k3_enumset1(X1,X1,X1,X1,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_24]), c_0_25]), c_0_27]), c_0_28])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_38])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (~m1_subset_1(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k1_zfmisc_1(esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_24]), c_0_25]), c_0_27]), c_0_28])).
% 0.13/0.38  cnf(c_0_50, plain, (~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.38  cnf(c_0_51, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (r2_hidden(esk3_0,k3_xboole_0(esk4_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.13/0.38  cnf(c_0_54, plain, (~r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_54]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 56
% 0.13/0.38  # Proof object clause steps            : 27
% 0.13/0.38  # Proof object formula steps           : 29
% 0.13/0.38  # Proof object conjectures             : 11
% 0.13/0.38  # Proof object clause conjectures      : 8
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 15
% 0.13/0.38  # Proof object initial formulas used   : 14
% 0.13/0.38  # Proof object generating inferences   : 6
% 0.13/0.38  # Proof object simplifying inferences  : 18
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 14
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 25
% 0.13/0.38  # Removed in clause preprocessing      : 5
% 0.13/0.38  # Initial clauses in saturation        : 20
% 0.13/0.38  # Processed clauses                    : 77
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 10
% 0.13/0.38  # ...remaining for further processing  : 66
% 0.13/0.38  # Other redundant clauses eliminated   : 1
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 18
% 0.13/0.38  # Generated clauses                    : 82
% 0.13/0.38  # ...of the previous two non-trivial   : 74
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 81
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 1
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 27
% 0.13/0.38  #    Positive orientable unit clauses  : 2
% 0.13/0.38  #    Positive unorientable unit clauses: 1
% 0.13/0.38  #    Negative unit clauses             : 4
% 0.13/0.38  #    Non-unit-clauses                  : 20
% 0.13/0.38  # Current number of unprocessed clauses: 34
% 0.13/0.38  # ...number of literals in the above   : 88
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 43
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 93
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 79
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.13/0.38  # Unit Clause-clause subsumption calls : 7
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 3
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2748
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
