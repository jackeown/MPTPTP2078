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
% DateTime   : Thu Dec  3 10:47:10 EST 2020

% Result     : Theorem 51.77s
% Output     : CNFRefutation 51.77s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 151 expanded)
%              Number of clauses        :   35 (  75 expanded)
%              Number of leaves         :   11 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  175 ( 517 expanded)
%              Number of equality atoms :   87 ( 298 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t8_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(k1_setfam_1(X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(c_0_11,plain,(
    ! [X21,X22] :
      ( ( r1_tarski(X21,X22)
        | X21 != X22 )
      & ( r1_tarski(X22,X21)
        | X21 != X22 )
      & ( ~ r1_tarski(X21,X22)
        | ~ r1_tarski(X22,X21)
        | X21 = X22 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X28,X27)
        | X28 = X24
        | X28 = X25
        | X28 = X26
        | X27 != k1_enumset1(X24,X25,X26) )
      & ( X29 != X24
        | r2_hidden(X29,X27)
        | X27 != k1_enumset1(X24,X25,X26) )
      & ( X29 != X25
        | r2_hidden(X29,X27)
        | X27 != k1_enumset1(X24,X25,X26) )
      & ( X29 != X26
        | r2_hidden(X29,X27)
        | X27 != k1_enumset1(X24,X25,X26) )
      & ( esk3_4(X30,X31,X32,X33) != X30
        | ~ r2_hidden(esk3_4(X30,X31,X32,X33),X33)
        | X33 = k1_enumset1(X30,X31,X32) )
      & ( esk3_4(X30,X31,X32,X33) != X31
        | ~ r2_hidden(esk3_4(X30,X31,X32,X33),X33)
        | X33 = k1_enumset1(X30,X31,X32) )
      & ( esk3_4(X30,X31,X32,X33) != X32
        | ~ r2_hidden(esk3_4(X30,X31,X32,X33),X33)
        | X33 = k1_enumset1(X30,X31,X32) )
      & ( r2_hidden(esk3_4(X30,X31,X32,X33),X33)
        | esk3_4(X30,X31,X32,X33) = X30
        | esk3_4(X30,X31,X32,X33) = X31
        | esk3_4(X30,X31,X32,X33) = X32
        | X33 = k1_enumset1(X30,X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_13,plain,(
    ! [X45,X46,X47] : k2_enumset1(X45,X45,X46,X47) = k1_enumset1(X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( r2_hidden(X15,X12)
        | ~ r2_hidden(X15,X14)
        | X14 != k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X16,X12)
        | r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk2_3(X17,X18,X19),X19)
        | ~ r2_hidden(esk2_3(X17,X18,X19),X17)
        | r2_hidden(esk2_3(X17,X18,X19),X18)
        | X19 = k4_xboole_0(X17,X18) )
      & ( r2_hidden(esk2_3(X17,X18,X19),X17)
        | r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk2_3(X17,X18,X19),X18)
        | r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k4_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_15,plain,(
    ! [X51,X52,X53] :
      ( ~ r2_hidden(X51,X52)
      | ~ r1_tarski(X51,X53)
      | r1_tarski(k1_setfam_1(X52),X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X23] : k4_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_setfam_1(X2),X3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_setfam_1(X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[c_0_24,c_0_18])).

fof(c_0_31,plain,(
    ! [X48,X49] :
      ( ( r2_hidden(esk5_2(X48,X49),X48)
        | X48 = k1_xboole_0
        | r1_tarski(X49,k1_setfam_1(X48)) )
      & ( ~ r1_tarski(X49,esk5_2(X48,X49))
        | X48 = k1_xboole_0
        | r1_tarski(X49,k1_setfam_1(X48)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_33,plain,(
    ! [X35,X36,X37,X38,X39,X40] :
      ( ( ~ r2_hidden(X37,X36)
        | X37 = X35
        | X36 != k1_tarski(X35) )
      & ( X38 != X35
        | r2_hidden(X38,X36)
        | X36 != k1_tarski(X35) )
      & ( ~ r2_hidden(esk4_2(X39,X40),X40)
        | esk4_2(X39,X40) != X39
        | X40 = k1_tarski(X39) )
      & ( r2_hidden(esk4_2(X39,X40),X40)
        | esk4_2(X39,X40) = X39
        | X40 = k1_tarski(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_34,plain,(
    ! [X42] : k2_tarski(X42,X42) = k1_tarski(X42) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_35,plain,(
    ! [X43,X44] : k1_enumset1(X43,X43,X44) = k2_tarski(X43,X44) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_36,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk6_0)) != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).

cnf(c_0_40,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_42,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk6_0)) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X2,X3)) = X3
    | ~ r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( r2_hidden(esk5_2(k2_enumset1(X1,X1,X2,X3),X4),k2_enumset1(X1,X1,X2,X3))
    | r1_tarski(X4,k1_setfam_1(k2_enumset1(X1,X1,X2,X3))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_48,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) != esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_43]),c_0_44]),c_0_18])).

cnf(c_0_50,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X2,X3)) = X3
    | r2_hidden(esk5_2(k2_enumset1(X1,X1,X2,X3),X3),k2_enumset1(X1,X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk5_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk6_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk5_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_54,negated_conjecture,
    ( esk5_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk6_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) = k1_xboole_0
    | r1_tarski(esk6_0,k1_setfam_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_22])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk6_0,k1_setfam_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_55]),c_0_41])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_56]),c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:37:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 51.77/51.94  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 51.77/51.94  # and selection function SelectNegativeLiterals.
% 51.77/51.94  #
% 51.77/51.94  # Preprocessing time       : 0.028 s
% 51.77/51.94  # Presaturation interreduction done
% 51.77/51.94  
% 51.77/51.94  # Proof found!
% 51.77/51.94  # SZS status Theorem
% 51.77/51.94  # SZS output start CNFRefutation
% 51.77/51.94  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 51.77/51.94  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 51.77/51.94  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 51.77/51.94  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 51.77/51.94  fof(t8_setfam_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(k1_setfam_1(X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_setfam_1)).
% 51.77/51.94  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 51.77/51.94  fof(t11_setfam_1, conjecture, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 51.77/51.94  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 51.77/51.94  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 51.77/51.94  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 51.77/51.94  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 51.77/51.94  fof(c_0_11, plain, ![X21, X22]:(((r1_tarski(X21,X22)|X21!=X22)&(r1_tarski(X22,X21)|X21!=X22))&(~r1_tarski(X21,X22)|~r1_tarski(X22,X21)|X21=X22)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 51.77/51.94  fof(c_0_12, plain, ![X24, X25, X26, X27, X28, X29, X30, X31, X32, X33]:(((~r2_hidden(X28,X27)|(X28=X24|X28=X25|X28=X26)|X27!=k1_enumset1(X24,X25,X26))&(((X29!=X24|r2_hidden(X29,X27)|X27!=k1_enumset1(X24,X25,X26))&(X29!=X25|r2_hidden(X29,X27)|X27!=k1_enumset1(X24,X25,X26)))&(X29!=X26|r2_hidden(X29,X27)|X27!=k1_enumset1(X24,X25,X26))))&((((esk3_4(X30,X31,X32,X33)!=X30|~r2_hidden(esk3_4(X30,X31,X32,X33),X33)|X33=k1_enumset1(X30,X31,X32))&(esk3_4(X30,X31,X32,X33)!=X31|~r2_hidden(esk3_4(X30,X31,X32,X33),X33)|X33=k1_enumset1(X30,X31,X32)))&(esk3_4(X30,X31,X32,X33)!=X32|~r2_hidden(esk3_4(X30,X31,X32,X33),X33)|X33=k1_enumset1(X30,X31,X32)))&(r2_hidden(esk3_4(X30,X31,X32,X33),X33)|(esk3_4(X30,X31,X32,X33)=X30|esk3_4(X30,X31,X32,X33)=X31|esk3_4(X30,X31,X32,X33)=X32)|X33=k1_enumset1(X30,X31,X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 51.77/51.94  fof(c_0_13, plain, ![X45, X46, X47]:k2_enumset1(X45,X45,X46,X47)=k1_enumset1(X45,X46,X47), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 51.77/51.94  fof(c_0_14, plain, ![X12, X13, X14, X15, X16, X17, X18, X19]:((((r2_hidden(X15,X12)|~r2_hidden(X15,X14)|X14!=k4_xboole_0(X12,X13))&(~r2_hidden(X15,X13)|~r2_hidden(X15,X14)|X14!=k4_xboole_0(X12,X13)))&(~r2_hidden(X16,X12)|r2_hidden(X16,X13)|r2_hidden(X16,X14)|X14!=k4_xboole_0(X12,X13)))&((~r2_hidden(esk2_3(X17,X18,X19),X19)|(~r2_hidden(esk2_3(X17,X18,X19),X17)|r2_hidden(esk2_3(X17,X18,X19),X18))|X19=k4_xboole_0(X17,X18))&((r2_hidden(esk2_3(X17,X18,X19),X17)|r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k4_xboole_0(X17,X18))&(~r2_hidden(esk2_3(X17,X18,X19),X18)|r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k4_xboole_0(X17,X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 51.77/51.94  fof(c_0_15, plain, ![X51, X52, X53]:(~r2_hidden(X51,X52)|~r1_tarski(X51,X53)|r1_tarski(k1_setfam_1(X52),X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).
% 51.77/51.94  cnf(c_0_16, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 51.77/51.94  cnf(c_0_17, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 51.77/51.94  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 51.77/51.94  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 51.77/51.94  fof(c_0_20, plain, ![X23]:k4_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t3_boole])).
% 51.77/51.94  cnf(c_0_21, plain, (r1_tarski(k1_setfam_1(X2),X3)|~r2_hidden(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 51.77/51.94  cnf(c_0_22, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_16])).
% 51.77/51.94  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X5,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 51.77/51.94  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 51.77/51.94  cnf(c_0_25, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_19])).
% 51.77/51.94  cnf(c_0_26, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 51.77/51.94  fof(c_0_27, negated_conjecture, ~(![X1]:k1_setfam_1(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t11_setfam_1])).
% 51.77/51.94  cnf(c_0_28, plain, (r1_tarski(k1_setfam_1(X1),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 51.77/51.94  cnf(c_0_29, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).
% 51.77/51.94  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X4,X5)), inference(rw,[status(thm)],[c_0_24, c_0_18])).
% 51.77/51.94  fof(c_0_31, plain, ![X48, X49]:((r2_hidden(esk5_2(X48,X49),X48)|(X48=k1_xboole_0|r1_tarski(X49,k1_setfam_1(X48))))&(~r1_tarski(X49,esk5_2(X48,X49))|(X48=k1_xboole_0|r1_tarski(X49,k1_setfam_1(X48))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 51.77/51.94  cnf(c_0_32, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 51.77/51.94  fof(c_0_33, plain, ![X35, X36, X37, X38, X39, X40]:(((~r2_hidden(X37,X36)|X37=X35|X36!=k1_tarski(X35))&(X38!=X35|r2_hidden(X38,X36)|X36!=k1_tarski(X35)))&((~r2_hidden(esk4_2(X39,X40),X40)|esk4_2(X39,X40)!=X39|X40=k1_tarski(X39))&(r2_hidden(esk4_2(X39,X40),X40)|esk4_2(X39,X40)=X39|X40=k1_tarski(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 51.77/51.94  fof(c_0_34, plain, ![X42]:k2_tarski(X42,X42)=k1_tarski(X42), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 51.77/51.94  fof(c_0_35, plain, ![X43, X44]:k1_enumset1(X43,X43,X44)=k2_tarski(X43,X44), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 51.77/51.94  fof(c_0_36, negated_conjecture, k1_setfam_1(k1_tarski(esk6_0))!=esk6_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 51.77/51.94  cnf(c_0_37, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 51.77/51.94  cnf(c_0_38, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X3)),X3)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 51.77/51.94  cnf(c_0_39, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).
% 51.77/51.94  cnf(c_0_40, plain, (r2_hidden(esk5_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 51.77/51.94  cnf(c_0_41, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_29])).
% 51.77/51.94  cnf(c_0_42, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 51.77/51.94  cnf(c_0_43, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 51.77/51.94  cnf(c_0_44, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 51.77/51.94  cnf(c_0_45, negated_conjecture, (k1_setfam_1(k1_tarski(esk6_0))!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 51.77/51.94  cnf(c_0_46, plain, (k1_setfam_1(k2_enumset1(X1,X1,X2,X3))=X3|~r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X2,X3)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 51.77/51.94  cnf(c_0_47, plain, (r2_hidden(esk5_2(k2_enumset1(X1,X1,X2,X3),X4),k2_enumset1(X1,X1,X2,X3))|r1_tarski(X4,k1_setfam_1(k2_enumset1(X1,X1,X2,X3)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 51.77/51.94  cnf(c_0_48, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_18])).
% 51.77/51.94  cnf(c_0_49, negated_conjecture, (k1_setfam_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))!=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_43]), c_0_44]), c_0_18])).
% 51.77/51.94  cnf(c_0_50, plain, (k1_setfam_1(k2_enumset1(X1,X1,X2,X3))=X3|r2_hidden(esk5_2(k2_enumset1(X1,X1,X2,X3),X3),k2_enumset1(X1,X1,X2,X3))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 51.77/51.94  cnf(c_0_51, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_48])).
% 51.77/51.94  cnf(c_0_52, negated_conjecture, (r2_hidden(esk5_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk6_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 51.77/51.94  cnf(c_0_53, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk5_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 51.77/51.94  cnf(c_0_54, negated_conjecture, (esk5_2(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk6_0)=esk6_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 51.77/51.94  cnf(c_0_55, negated_conjecture, (k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)=k1_xboole_0|r1_tarski(esk6_0,k1_setfam_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_22])])).
% 51.77/51.94  cnf(c_0_56, negated_conjecture, (r1_tarski(esk6_0,k1_setfam_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_55]), c_0_41])).
% 51.77/51.94  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_56]), c_0_49]), ['proof']).
% 51.77/51.94  # SZS output end CNFRefutation
% 51.77/51.94  # Proof object total steps             : 58
% 51.77/51.94  # Proof object clause steps            : 35
% 51.77/51.94  # Proof object formula steps           : 23
% 51.77/51.94  # Proof object conjectures             : 10
% 51.77/51.94  # Proof object clause conjectures      : 7
% 51.77/51.94  # Proof object formula conjectures     : 3
% 51.77/51.94  # Proof object initial clauses used    : 14
% 51.77/51.94  # Proof object initial formulas used   : 11
% 51.77/51.94  # Proof object generating inferences   : 12
% 51.77/51.94  # Proof object simplifying inferences  : 20
% 51.77/51.94  # Training examples: 0 positive, 0 negative
% 51.77/51.94  # Parsed axioms                        : 12
% 51.77/51.94  # Removed by relevancy pruning/SinE    : 0
% 51.77/51.94  # Initial clauses                      : 32
% 51.77/51.94  # Removed in clause preprocessing      : 3
% 51.77/51.94  # Initial clauses in saturation        : 29
% 51.77/51.94  # Processed clauses                    : 24060
% 51.77/51.94  # ...of these trivial                  : 466
% 51.77/51.94  # ...subsumed                          : 16877
% 51.77/51.94  # ...remaining for further processing  : 6717
% 51.77/51.94  # Other redundant clauses eliminated   : 28062
% 51.77/51.94  # Clauses deleted for lack of memory   : 73297
% 51.77/51.94  # Backward-subsumed                    : 186
% 51.77/51.94  # Backward-rewritten                   : 31
% 51.77/51.94  # Generated clauses                    : 5301131
% 51.77/51.94  # ...of the previous two non-trivial   : 4946792
% 51.77/51.94  # Contextual simplify-reflections      : 54
% 51.77/51.94  # Paramodulations                      : 5272280
% 51.77/51.94  # Factorizations                       : 793
% 51.77/51.94  # Equation resolutions                 : 28062
% 51.77/51.94  # Propositional unsat checks           : 0
% 51.77/51.94  #    Propositional check models        : 0
% 51.77/51.94  #    Propositional check unsatisfiable : 0
% 51.77/51.94  #    Propositional clauses             : 0
% 51.77/51.94  #    Propositional clauses after purity: 0
% 51.77/51.94  #    Propositional unsat core size     : 0
% 51.77/51.94  #    Propositional preprocessing time  : 0.000
% 51.77/51.94  #    Propositional encoding time       : 0.000
% 51.77/51.94  #    Propositional solver time         : 0.000
% 51.77/51.94  #    Success case prop preproc time    : 0.000
% 51.77/51.94  #    Success case prop encoding time   : 0.000
% 51.77/51.94  #    Success case prop solver time     : 0.000
% 51.77/51.94  # Current number of processed clauses  : 6462
% 51.77/51.94  #    Positive orientable unit clauses  : 160
% 51.77/51.94  #    Positive unorientable unit clauses: 0
% 51.77/51.94  #    Negative unit clauses             : 2
% 51.77/51.94  #    Non-unit-clauses                  : 6300
% 51.77/51.94  # Current number of unprocessed clauses: 1657006
% 51.77/51.94  # ...number of literals in the above   : 8277415
% 51.77/51.94  # Current number of archived formulas  : 0
% 51.77/51.94  # Current number of archived clauses   : 247
% 51.77/51.94  # Clause-clause subsumption calls (NU) : 3212648
% 51.77/51.94  # Rec. Clause-clause subsumption calls : 967391
% 51.77/51.94  # Non-unit clause-clause subsumptions  : 15687
% 51.77/51.94  # Unit Clause-clause subsumption calls : 18393
% 51.77/51.94  # Rewrite failures with RHS unbound    : 0
% 51.77/51.94  # BW rewrite match attempts            : 1059
% 51.77/51.94  # BW rewrite match successes           : 10
% 51.77/51.94  # Condensation attempts                : 0
% 51.77/51.94  # Condensation successes               : 0
% 51.77/51.94  # Termbank termtop insertions          : 139854950
% 51.77/52.02  
% 51.77/52.02  # -------------------------------------------------
% 51.77/52.02  # User time                : 50.618 s
% 51.77/52.02  # System time              : 1.050 s
% 51.77/52.02  # Total time               : 51.669 s
% 51.77/52.02  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
