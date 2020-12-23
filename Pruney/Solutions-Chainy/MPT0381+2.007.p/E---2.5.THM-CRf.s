%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:54 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 189 expanded)
%              Number of clauses        :   34 (  80 expanded)
%              Number of leaves         :   15 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :  136 ( 376 expanded)
%              Number of equality atoms :   38 ( 121 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t63_subset_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t55_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ( X1 != k1_xboole_0
       => m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(c_0_15,plain,(
    ! [X25,X26,X27,X28,X29,X30] :
      ( ( ~ r2_hidden(X27,X26)
        | r1_tarski(X27,X25)
        | X26 != k1_zfmisc_1(X25) )
      & ( ~ r1_tarski(X28,X25)
        | r2_hidden(X28,X26)
        | X26 != k1_zfmisc_1(X25) )
      & ( ~ r2_hidden(esk3_2(X29,X30),X30)
        | ~ r1_tarski(esk3_2(X29,X30),X29)
        | X30 = k1_zfmisc_1(X29) )
      & ( r2_hidden(esk3_2(X29,X30),X30)
        | r1_tarski(esk3_2(X29,X30),X29)
        | X30 = k1_zfmisc_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_16,plain,(
    ! [X35,X36] :
      ( ( ~ m1_subset_1(X36,X35)
        | r2_hidden(X36,X35)
        | v1_xboole_0(X35) )
      & ( ~ r2_hidden(X36,X35)
        | m1_subset_1(X36,X35)
        | v1_xboole_0(X35) )
      & ( ~ m1_subset_1(X36,X35)
        | v1_xboole_0(X36)
        | ~ v1_xboole_0(X35) )
      & ( ~ v1_xboole_0(X36)
        | m1_subset_1(X36,X35)
        | ~ v1_xboole_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_17,plain,(
    ! [X38] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X38)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_18,plain,(
    ! [X37] : ~ v1_xboole_0(k1_zfmisc_1(X37)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_19,plain,(
    ! [X32,X33,X34] :
      ( ( r2_hidden(X32,X33)
        | ~ r2_hidden(X32,k4_xboole_0(X33,k1_tarski(X34))) )
      & ( X32 != X34
        | ~ r2_hidden(X32,k4_xboole_0(X33,k1_tarski(X34))) )
      & ( ~ r2_hidden(X32,X33)
        | X32 = X34
        | r2_hidden(X32,k4_xboole_0(X33,k1_tarski(X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_20,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(X11,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_23,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_29,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    inference(assume_negation,[status(cth)],[t63_subset_1])).

cnf(c_0_31,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_37,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | k3_xboole_0(X13,X14) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

fof(c_0_40,plain,(
    ! [X39,X40] :
      ( ~ m1_subset_1(X40,X39)
      | X39 = k1_xboole_0
      | m1_subset_1(k1_tarski(X40),k1_zfmisc_1(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_subset_1])])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_43,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    & ~ m1_subset_1(k1_tarski(esk4_0),k1_zfmisc_1(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).

cnf(c_0_44,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k5_xboole_0(X3,k3_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_48,plain,
    ( X2 = k1_xboole_0
    | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( ~ m1_subset_1(k1_tarski(esk4_0),k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)))) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_54,plain,(
    ! [X9] :
      ( X9 = k1_xboole_0
      | r2_hidden(esk2_1(X9),X9) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_55,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_47])).

cnf(c_0_56,plain,
    ( X2 = k1_xboole_0
    | m1_subset_1(k3_enumset1(X1,X1,X1,X1,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_32]),c_0_33]),c_0_35]),c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( ~ m1_subset_1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k1_zfmisc_1(esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_32]),c_0_33]),c_0_35]),c_0_36])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_1(esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_62]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 11:38:44 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.11/0.34  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.11/0.34  # and selection function SelectNegativeLiterals.
% 0.11/0.34  #
% 0.11/0.34  # Preprocessing time       : 0.016 s
% 0.11/0.34  # Presaturation interreduction done
% 0.11/0.34  
% 0.11/0.34  # Proof found!
% 0.11/0.34  # SZS status Theorem
% 0.11/0.34  # SZS output start CNFRefutation
% 0.11/0.34  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.11/0.34  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.11/0.34  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.11/0.34  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.11/0.34  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.11/0.34  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.11/0.34  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.11/0.34  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.11/0.34  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.11/0.34  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.11/0.34  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.11/0.34  fof(t63_subset_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 0.11/0.34  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.11/0.34  fof(t55_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 0.11/0.34  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.11/0.34  fof(c_0_15, plain, ![X25, X26, X27, X28, X29, X30]:(((~r2_hidden(X27,X26)|r1_tarski(X27,X25)|X26!=k1_zfmisc_1(X25))&(~r1_tarski(X28,X25)|r2_hidden(X28,X26)|X26!=k1_zfmisc_1(X25)))&((~r2_hidden(esk3_2(X29,X30),X30)|~r1_tarski(esk3_2(X29,X30),X29)|X30=k1_zfmisc_1(X29))&(r2_hidden(esk3_2(X29,X30),X30)|r1_tarski(esk3_2(X29,X30),X29)|X30=k1_zfmisc_1(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.11/0.34  fof(c_0_16, plain, ![X35, X36]:(((~m1_subset_1(X36,X35)|r2_hidden(X36,X35)|v1_xboole_0(X35))&(~r2_hidden(X36,X35)|m1_subset_1(X36,X35)|v1_xboole_0(X35)))&((~m1_subset_1(X36,X35)|v1_xboole_0(X36)|~v1_xboole_0(X35))&(~v1_xboole_0(X36)|m1_subset_1(X36,X35)|~v1_xboole_0(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.11/0.34  fof(c_0_17, plain, ![X38]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X38)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.11/0.34  fof(c_0_18, plain, ![X37]:~v1_xboole_0(k1_zfmisc_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.11/0.34  fof(c_0_19, plain, ![X32, X33, X34]:(((r2_hidden(X32,X33)|~r2_hidden(X32,k4_xboole_0(X33,k1_tarski(X34))))&(X32!=X34|~r2_hidden(X32,k4_xboole_0(X33,k1_tarski(X34)))))&(~r2_hidden(X32,X33)|X32=X34|r2_hidden(X32,k4_xboole_0(X33,k1_tarski(X34))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.11/0.34  fof(c_0_20, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.11/0.34  fof(c_0_21, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.11/0.34  fof(c_0_22, plain, ![X11, X12]:k4_xboole_0(X11,X12)=k5_xboole_0(X11,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.11/0.34  fof(c_0_23, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.11/0.34  fof(c_0_24, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.11/0.34  cnf(c_0_25, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.34  cnf(c_0_26, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.11/0.34  cnf(c_0_27, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.11/0.34  cnf(c_0_28, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.11/0.34  fof(c_0_29, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.11/0.34  fof(c_0_30, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)))), inference(assume_negation,[status(cth)],[t63_subset_1])).
% 0.11/0.34  cnf(c_0_31, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.11/0.34  cnf(c_0_32, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.11/0.34  cnf(c_0_33, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.11/0.34  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.11/0.34  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.11/0.34  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.11/0.34  fof(c_0_37, plain, ![X13, X14]:(~r1_tarski(X13,X14)|k3_xboole_0(X13,X14)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.11/0.34  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_25])).
% 0.11/0.34  cnf(c_0_39, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.11/0.34  fof(c_0_40, plain, ![X39, X40]:(~m1_subset_1(X40,X39)|(X39=k1_xboole_0|m1_subset_1(k1_tarski(X40),k1_zfmisc_1(X39)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_subset_1])])).
% 0.11/0.34  cnf(c_0_41, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.11/0.34  cnf(c_0_42, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.11/0.34  fof(c_0_43, negated_conjecture, (r2_hidden(esk4_0,esk5_0)&~m1_subset_1(k1_tarski(esk4_0),k1_zfmisc_1(esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).
% 0.11/0.34  cnf(c_0_44, plain, (X1!=X2|~r2_hidden(X1,k5_xboole_0(X3,k3_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 0.11/0.34  cnf(c_0_45, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.11/0.34  cnf(c_0_46, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.11/0.34  cnf(c_0_47, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.11/0.34  cnf(c_0_48, plain, (X2=k1_xboole_0|m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.11/0.34  cnf(c_0_49, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_41, c_0_42])).
% 0.11/0.34  cnf(c_0_50, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.11/0.34  cnf(c_0_51, negated_conjecture, (~m1_subset_1(k1_tarski(esk4_0),k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.11/0.34  cnf(c_0_52, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1))))), inference(er,[status(thm)],[c_0_44])).
% 0.11/0.34  cnf(c_0_53, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.11/0.34  fof(c_0_54, plain, ![X9]:(X9=k1_xboole_0|r2_hidden(esk2_1(X9),X9)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.11/0.34  cnf(c_0_55, plain, (r2_hidden(esk1_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_47])).
% 0.11/0.34  cnf(c_0_56, plain, (X2=k1_xboole_0|m1_subset_1(k3_enumset1(X1,X1,X1,X1,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_32]), c_0_33]), c_0_35]), c_0_36])).
% 0.11/0.34  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.11/0.34  cnf(c_0_58, negated_conjecture, (~m1_subset_1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k1_zfmisc_1(esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_32]), c_0_33]), c_0_35]), c_0_36])).
% 0.11/0.34  cnf(c_0_59, plain, (~r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.11/0.34  cnf(c_0_60, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.11/0.34  cnf(c_0_61, negated_conjecture, (r2_hidden(esk1_1(esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_55, c_0_50])).
% 0.11/0.34  cnf(c_0_62, negated_conjecture, (esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.11/0.34  cnf(c_0_63, plain, (~r2_hidden(X1,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_59])).
% 0.11/0.34  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_62]), c_0_63]), ['proof']).
% 0.11/0.34  # SZS output end CNFRefutation
% 0.11/0.34  # Proof object total steps             : 65
% 0.11/0.34  # Proof object clause steps            : 34
% 0.11/0.34  # Proof object formula steps           : 31
% 0.11/0.34  # Proof object conjectures             : 10
% 0.11/0.34  # Proof object clause conjectures      : 7
% 0.11/0.34  # Proof object formula conjectures     : 3
% 0.11/0.34  # Proof object initial clauses used    : 18
% 0.11/0.34  # Proof object initial formulas used   : 15
% 0.11/0.34  # Proof object generating inferences   : 9
% 0.11/0.34  # Proof object simplifying inferences  : 22
% 0.11/0.34  # Training examples: 0 positive, 0 negative
% 0.11/0.34  # Parsed axioms                        : 15
% 0.11/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.34  # Initial clauses                      : 25
% 0.11/0.34  # Removed in clause preprocessing      : 5
% 0.11/0.34  # Initial clauses in saturation        : 20
% 0.11/0.34  # Processed clauses                    : 73
% 0.11/0.34  # ...of these trivial                  : 4
% 0.11/0.34  # ...subsumed                          : 3
% 0.11/0.34  # ...remaining for further processing  : 66
% 0.11/0.34  # Other redundant clauses eliminated   : 3
% 0.11/0.34  # Clauses deleted for lack of memory   : 0
% 0.11/0.34  # Backward-subsumed                    : 0
% 0.11/0.34  # Backward-rewritten                   : 18
% 0.11/0.34  # Generated clauses                    : 183
% 0.11/0.34  # ...of the previous two non-trivial   : 170
% 0.11/0.34  # Contextual simplify-reflections      : 1
% 0.11/0.34  # Paramodulations                      : 178
% 0.11/0.34  # Factorizations                       : 0
% 0.11/0.34  # Equation resolutions                 : 3
% 0.11/0.34  # Propositional unsat checks           : 0
% 0.11/0.34  #    Propositional check models        : 0
% 0.11/0.34  #    Propositional check unsatisfiable : 0
% 0.11/0.34  #    Propositional clauses             : 0
% 0.11/0.34  #    Propositional clauses after purity: 0
% 0.11/0.34  #    Propositional unsat core size     : 0
% 0.11/0.34  #    Propositional preprocessing time  : 0.000
% 0.11/0.34  #    Propositional encoding time       : 0.000
% 0.11/0.34  #    Propositional solver time         : 0.000
% 0.11/0.34  #    Success case prop preproc time    : 0.000
% 0.11/0.34  #    Success case prop encoding time   : 0.000
% 0.11/0.34  #    Success case prop solver time     : 0.000
% 0.11/0.34  # Current number of processed clauses  : 23
% 0.11/0.34  #    Positive orientable unit clauses  : 5
% 0.11/0.34  #    Positive unorientable unit clauses: 0
% 0.11/0.34  #    Negative unit clauses             : 4
% 0.11/0.34  #    Non-unit-clauses                  : 14
% 0.11/0.34  # Current number of unprocessed clauses: 130
% 0.11/0.34  # ...number of literals in the above   : 366
% 0.11/0.34  # Current number of archived formulas  : 0
% 0.11/0.34  # Current number of archived clauses   : 45
% 0.11/0.34  # Clause-clause subsumption calls (NU) : 78
% 0.11/0.34  # Rec. Clause-clause subsumption calls : 69
% 0.11/0.34  # Non-unit clause-clause subsumptions  : 2
% 0.11/0.34  # Unit Clause-clause subsumption calls : 42
% 0.11/0.34  # Rewrite failures with RHS unbound    : 0
% 0.11/0.34  # BW rewrite match attempts            : 3
% 0.11/0.34  # BW rewrite match successes           : 3
% 0.11/0.34  # Condensation attempts                : 0
% 0.11/0.34  # Condensation successes               : 0
% 0.11/0.34  # Termbank termtop insertions          : 3291
% 0.11/0.34  
% 0.11/0.34  # -------------------------------------------------
% 0.11/0.34  # User time                : 0.022 s
% 0.11/0.34  # System time              : 0.000 s
% 0.11/0.34  # Total time               : 0.022 s
% 0.11/0.34  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
