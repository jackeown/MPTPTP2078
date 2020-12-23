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
% DateTime   : Thu Dec  3 10:47:11 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 404 expanded)
%              Number of clauses        :   39 ( 178 expanded)
%              Number of leaves         :   12 ( 110 expanded)
%              Depth                    :   15
%              Number of atoms          :  155 ( 949 expanded)
%              Number of equality atoms :   86 ( 647 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(t5_setfam_1,axiom,(
    ! [X1] :
      ( r2_hidden(k1_xboole_0,X1)
     => k1_setfam_1(X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t6_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(t3_setfam_1,axiom,(
    ! [X1] : r1_tarski(k1_setfam_1(X1),k3_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_setfam_1)).

fof(c_0_12,plain,(
    ! [X23,X24,X25,X26,X27,X28,X29,X30,X31,X32] :
      ( ( ~ r2_hidden(X27,X26)
        | X27 = X23
        | X27 = X24
        | X27 = X25
        | X26 != k1_enumset1(X23,X24,X25) )
      & ( X28 != X23
        | r2_hidden(X28,X26)
        | X26 != k1_enumset1(X23,X24,X25) )
      & ( X28 != X24
        | r2_hidden(X28,X26)
        | X26 != k1_enumset1(X23,X24,X25) )
      & ( X28 != X25
        | r2_hidden(X28,X26)
        | X26 != k1_enumset1(X23,X24,X25) )
      & ( esk3_4(X29,X30,X31,X32) != X29
        | ~ r2_hidden(esk3_4(X29,X30,X31,X32),X32)
        | X32 = k1_enumset1(X29,X30,X31) )
      & ( esk3_4(X29,X30,X31,X32) != X30
        | ~ r2_hidden(esk3_4(X29,X30,X31,X32),X32)
        | X32 = k1_enumset1(X29,X30,X31) )
      & ( esk3_4(X29,X30,X31,X32) != X31
        | ~ r2_hidden(esk3_4(X29,X30,X31,X32),X32)
        | X32 = k1_enumset1(X29,X30,X31) )
      & ( r2_hidden(esk3_4(X29,X30,X31,X32),X32)
        | esk3_4(X29,X30,X31,X32) = X29
        | esk3_4(X29,X30,X31,X32) = X30
        | esk3_4(X29,X30,X31,X32) = X31
        | X32 = k1_enumset1(X29,X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_13,plain,(
    ! [X37,X38,X39] : k2_enumset1(X37,X37,X38,X39) = k1_enumset1(X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X46,X47] :
      ( ~ r2_hidden(X46,X47)
      | r1_tarski(k1_setfam_1(X47),X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X48] :
      ( ~ r2_hidden(k1_xboole_0,X48)
      | k1_setfam_1(X48) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_setfam_1])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[c_0_16,c_0_15])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

fof(c_0_22,plain,(
    ! [X43,X44] :
      ( ~ r1_tarski(k1_tarski(X43),k1_tarski(X44))
      | X43 = X44 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).

fof(c_0_23,plain,(
    ! [X34] : k2_tarski(X34,X34) = k1_tarski(X34) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_24,plain,(
    ! [X35,X36] : k1_enumset1(X35,X35,X36) = k2_tarski(X35,X36) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).

cnf(c_0_27,plain,
    ( k1_setfam_1(X1) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).

fof(c_0_29,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk5_0)) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r1_tarski(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X49,X50] :
      ( ( r2_hidden(esk4_2(X49,X50),X49)
        | X49 = k1_xboole_0
        | r1_tarski(X50,k1_setfam_1(X49)) )
      & ( ~ r1_tarski(X50,esk4_2(X49,X50))
        | X49 = k1_xboole_0
        | r1_tarski(X50,k1_setfam_1(X49)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk5_0)) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_15]),c_0_15])).

cnf(c_0_38,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_40,plain,(
    ! [X21,X22] :
      ( ( r1_tarski(X21,X22)
        | X21 != X22 )
      & ( r1_tarski(X22,X21)
        | X21 != X22 )
      & ( ~ r1_tarski(X21,X22)
        | ~ r1_tarski(X22,X21)
        | X21 = X22 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_41,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_31]),c_0_32]),c_0_15])).

cnf(c_0_42,plain,
    ( X1 = X2
    | r2_hidden(esk4_2(k2_enumset1(X1,X1,X1,X1),X3),k2_enumset1(X1,X1,X1,X1))
    | r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

fof(c_0_43,plain,(
    ! [X42] : k3_tarski(k1_tarski(X42)) = X42 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

cnf(c_0_44,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk4_2(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),X1),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))
    | r1_tarski(X1,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42])])).

fof(c_0_47,plain,(
    ! [X45] : r1_tarski(k1_setfam_1(X45),k3_tarski(X45)) ),
    inference(variable_rename,[status(thm)],[t3_setfam_1])).

cnf(c_0_48,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( X1 = k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk4_2(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),X1),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_setfam_1(X1),k3_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_31]),c_0_32]),c_0_15])).

cnf(c_0_53,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k2_enumset1(X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk4_2(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk5_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_52]),c_0_41])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_56,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk4_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_57,negated_conjecture,
    ( esk4_2(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk5_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0
    | r1_tarski(esk5_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_60,negated_conjecture,
    ( esk5_0 = X1
    | r1_tarski(esk5_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_59]),c_0_39])])).

cnf(c_0_61,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X2,X3)) = X3
    | ~ r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_34])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk5_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_60]),c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:29:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.48/0.67  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.48/0.67  # and selection function SelectNegativeLiterals.
% 0.48/0.67  #
% 0.48/0.67  # Preprocessing time       : 0.038 s
% 0.48/0.67  # Presaturation interreduction done
% 0.48/0.67  
% 0.48/0.67  # Proof found!
% 0.48/0.67  # SZS status Theorem
% 0.48/0.67  # SZS output start CNFRefutation
% 0.48/0.67  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.48/0.67  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.48/0.67  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.48/0.67  fof(t5_setfam_1, axiom, ![X1]:(r2_hidden(k1_xboole_0,X1)=>k1_setfam_1(X1)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_setfam_1)).
% 0.48/0.67  fof(t11_setfam_1, conjecture, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.48/0.67  fof(t6_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 0.48/0.67  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.48/0.67  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.48/0.67  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 0.48/0.67  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.48/0.67  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.48/0.67  fof(t3_setfam_1, axiom, ![X1]:r1_tarski(k1_setfam_1(X1),k3_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_setfam_1)).
% 0.48/0.67  fof(c_0_12, plain, ![X23, X24, X25, X26, X27, X28, X29, X30, X31, X32]:(((~r2_hidden(X27,X26)|(X27=X23|X27=X24|X27=X25)|X26!=k1_enumset1(X23,X24,X25))&(((X28!=X23|r2_hidden(X28,X26)|X26!=k1_enumset1(X23,X24,X25))&(X28!=X24|r2_hidden(X28,X26)|X26!=k1_enumset1(X23,X24,X25)))&(X28!=X25|r2_hidden(X28,X26)|X26!=k1_enumset1(X23,X24,X25))))&((((esk3_4(X29,X30,X31,X32)!=X29|~r2_hidden(esk3_4(X29,X30,X31,X32),X32)|X32=k1_enumset1(X29,X30,X31))&(esk3_4(X29,X30,X31,X32)!=X30|~r2_hidden(esk3_4(X29,X30,X31,X32),X32)|X32=k1_enumset1(X29,X30,X31)))&(esk3_4(X29,X30,X31,X32)!=X31|~r2_hidden(esk3_4(X29,X30,X31,X32),X32)|X32=k1_enumset1(X29,X30,X31)))&(r2_hidden(esk3_4(X29,X30,X31,X32),X32)|(esk3_4(X29,X30,X31,X32)=X29|esk3_4(X29,X30,X31,X32)=X30|esk3_4(X29,X30,X31,X32)=X31)|X32=k1_enumset1(X29,X30,X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.48/0.67  fof(c_0_13, plain, ![X37, X38, X39]:k2_enumset1(X37,X37,X38,X39)=k1_enumset1(X37,X38,X39), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.48/0.67  cnf(c_0_14, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.67  cnf(c_0_15, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.48/0.67  cnf(c_0_16, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.67  fof(c_0_17, plain, ![X46, X47]:(~r2_hidden(X46,X47)|r1_tarski(k1_setfam_1(X47),X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.48/0.67  cnf(c_0_18, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X5,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.48/0.67  fof(c_0_19, plain, ![X48]:(~r2_hidden(k1_xboole_0,X48)|k1_setfam_1(X48)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_setfam_1])])).
% 0.48/0.67  cnf(c_0_20, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X4,X5)), inference(rw,[status(thm)],[c_0_16, c_0_15])).
% 0.48/0.67  fof(c_0_21, negated_conjecture, ~(![X1]:k1_setfam_1(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t11_setfam_1])).
% 0.48/0.67  fof(c_0_22, plain, ![X43, X44]:(~r1_tarski(k1_tarski(X43),k1_tarski(X44))|X43=X44), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).
% 0.48/0.67  fof(c_0_23, plain, ![X34]:k2_tarski(X34,X34)=k1_tarski(X34), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.48/0.67  fof(c_0_24, plain, ![X35, X36]:k1_enumset1(X35,X35,X36)=k2_tarski(X35,X36), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.48/0.67  cnf(c_0_25, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.48/0.67  cnf(c_0_26, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).
% 0.48/0.67  cnf(c_0_27, plain, (k1_setfam_1(X1)=k1_xboole_0|~r2_hidden(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.48/0.67  cnf(c_0_28, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).
% 0.48/0.67  fof(c_0_29, negated_conjecture, k1_setfam_1(k1_tarski(esk5_0))!=esk5_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.48/0.67  cnf(c_0_30, plain, (X1=X2|~r1_tarski(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.48/0.67  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.48/0.67  cnf(c_0_32, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.48/0.67  fof(c_0_33, plain, ![X49, X50]:((r2_hidden(esk4_2(X49,X50),X49)|(X49=k1_xboole_0|r1_tarski(X50,k1_setfam_1(X49))))&(~r1_tarski(X50,esk4_2(X49,X50))|(X49=k1_xboole_0|r1_tarski(X50,k1_setfam_1(X49))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 0.48/0.67  cnf(c_0_34, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X3)),X3)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.48/0.67  cnf(c_0_35, plain, (k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.48/0.67  cnf(c_0_36, negated_conjecture, (k1_setfam_1(k1_tarski(esk5_0))!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.48/0.67  cnf(c_0_37, plain, (X1=X2|~r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_15]), c_0_15])).
% 0.48/0.67  cnf(c_0_38, plain, (r2_hidden(esk4_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.48/0.67  cnf(c_0_39, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.48/0.67  fof(c_0_40, plain, ![X21, X22]:(((r1_tarski(X21,X22)|X21!=X22)&(r1_tarski(X22,X21)|X21!=X22))&(~r1_tarski(X21,X22)|~r1_tarski(X22,X21)|X21=X22)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.48/0.67  cnf(c_0_41, negated_conjecture, (k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_31]), c_0_32]), c_0_15])).
% 0.48/0.67  cnf(c_0_42, plain, (X1=X2|r2_hidden(esk4_2(k2_enumset1(X1,X1,X1,X1),X3),k2_enumset1(X1,X1,X1,X1))|r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.48/0.67  fof(c_0_43, plain, ![X42]:k3_tarski(k1_tarski(X42))=X42, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 0.48/0.67  cnf(c_0_44, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.67  cnf(c_0_45, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.48/0.67  cnf(c_0_46, negated_conjecture, (r2_hidden(esk4_2(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),X1),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))|r1_tarski(X1,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42])])).
% 0.48/0.67  fof(c_0_47, plain, ![X45]:r1_tarski(k1_setfam_1(X45),k3_tarski(X45)), inference(variable_rename,[status(thm)],[t3_setfam_1])).
% 0.48/0.67  cnf(c_0_48, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.48/0.67  cnf(c_0_49, plain, (X1=X5|X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_44, c_0_15])).
% 0.48/0.67  cnf(c_0_50, negated_conjecture, (X1=k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk4_2(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),X1),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))|~r1_tarski(k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.48/0.67  cnf(c_0_51, plain, (r1_tarski(k1_setfam_1(X1),k3_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.48/0.67  cnf(c_0_52, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_31]), c_0_32]), c_0_15])).
% 0.48/0.67  cnf(c_0_53, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k2_enumset1(X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_49])).
% 0.48/0.67  cnf(c_0_54, negated_conjecture, (r2_hidden(esk4_2(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk5_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_52]), c_0_41])).
% 0.48/0.67  cnf(c_0_55, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.48/0.67  cnf(c_0_56, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk4_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.48/0.67  cnf(c_0_57, negated_conjecture, (esk4_2(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk5_0)=esk5_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.48/0.67  cnf(c_0_58, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_55])).
% 0.48/0.67  cnf(c_0_59, negated_conjecture, (k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0|r1_tarski(esk5_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 0.48/0.67  cnf(c_0_60, negated_conjecture, (esk5_0=X1|r1_tarski(esk5_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_59]), c_0_39])])).
% 0.48/0.67  cnf(c_0_61, plain, (k1_setfam_1(k2_enumset1(X1,X1,X2,X3))=X3|~r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X2,X3)))), inference(spm,[status(thm)],[c_0_45, c_0_34])).
% 0.48/0.67  cnf(c_0_62, negated_conjecture, (r1_tarski(esk5_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_60]), c_0_60])).
% 0.48/0.67  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_41]), ['proof']).
% 0.48/0.67  # SZS output end CNFRefutation
% 0.48/0.67  # Proof object total steps             : 64
% 0.48/0.67  # Proof object clause steps            : 39
% 0.48/0.67  # Proof object formula steps           : 25
% 0.48/0.67  # Proof object conjectures             : 13
% 0.48/0.67  # Proof object clause conjectures      : 10
% 0.48/0.67  # Proof object formula conjectures     : 3
% 0.48/0.67  # Proof object initial clauses used    : 16
% 0.48/0.67  # Proof object initial formulas used   : 12
% 0.48/0.67  # Proof object generating inferences   : 13
% 0.48/0.67  # Proof object simplifying inferences  : 33
% 0.48/0.67  # Training examples: 0 positive, 0 negative
% 0.48/0.67  # Parsed axioms                        : 15
% 0.48/0.67  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.67  # Initial clauses                      : 33
% 0.48/0.67  # Removed in clause preprocessing      : 3
% 0.48/0.67  # Initial clauses in saturation        : 30
% 0.48/0.67  # Processed clauses                    : 633
% 0.48/0.67  # ...of these trivial                  : 20
% 0.48/0.67  # ...subsumed                          : 234
% 0.48/0.67  # ...remaining for further processing  : 379
% 0.48/0.67  # Other redundant clauses eliminated   : 225
% 0.48/0.67  # Clauses deleted for lack of memory   : 0
% 0.48/0.67  # Backward-subsumed                    : 12
% 0.48/0.67  # Backward-rewritten                   : 7
% 0.48/0.67  # Generated clauses                    : 24663
% 0.48/0.67  # ...of the previous two non-trivial   : 21878
% 0.48/0.67  # Contextual simplify-reflections      : 3
% 0.48/0.67  # Paramodulations                      : 24435
% 0.48/0.67  # Factorizations                       : 6
% 0.48/0.67  # Equation resolutions                 : 225
% 0.48/0.67  # Propositional unsat checks           : 0
% 0.48/0.67  #    Propositional check models        : 0
% 0.48/0.67  #    Propositional check unsatisfiable : 0
% 0.48/0.67  #    Propositional clauses             : 0
% 0.48/0.67  #    Propositional clauses after purity: 0
% 0.48/0.67  #    Propositional unsat core size     : 0
% 0.48/0.67  #    Propositional preprocessing time  : 0.000
% 0.48/0.67  #    Propositional encoding time       : 0.000
% 0.48/0.67  #    Propositional solver time         : 0.000
% 0.48/0.67  #    Success case prop preproc time    : 0.000
% 0.48/0.67  #    Success case prop encoding time   : 0.000
% 0.48/0.67  #    Success case prop solver time     : 0.000
% 0.48/0.67  # Current number of processed clauses  : 322
% 0.48/0.67  #    Positive orientable unit clauses  : 43
% 0.48/0.67  #    Positive unorientable unit clauses: 0
% 0.48/0.67  #    Negative unit clauses             : 1
% 0.48/0.67  #    Non-unit-clauses                  : 278
% 0.48/0.67  # Current number of unprocessed clauses: 21095
% 0.48/0.67  # ...number of literals in the above   : 86249
% 0.48/0.67  # Current number of archived formulas  : 0
% 0.48/0.67  # Current number of archived clauses   : 51
% 0.48/0.67  # Clause-clause subsumption calls (NU) : 8825
% 0.48/0.67  # Rec. Clause-clause subsumption calls : 5184
% 0.48/0.67  # Non-unit clause-clause subsumptions  : 249
% 0.48/0.67  # Unit Clause-clause subsumption calls : 238
% 0.48/0.67  # Rewrite failures with RHS unbound    : 0
% 0.48/0.67  # BW rewrite match attempts            : 53
% 0.48/0.67  # BW rewrite match successes           : 5
% 0.48/0.67  # Condensation attempts                : 0
% 0.48/0.67  # Condensation successes               : 0
% 0.48/0.67  # Termbank termtop insertions          : 432821
% 0.48/0.67  
% 0.48/0.67  # -------------------------------------------------
% 0.48/0.67  # User time                : 0.304 s
% 0.48/0.67  # System time              : 0.019 s
% 0.48/0.67  # Total time               : 0.323 s
% 0.48/0.67  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
