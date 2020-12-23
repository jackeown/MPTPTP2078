%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:01 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 124 expanded)
%              Number of clauses        :   30 (  52 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :  140 ( 236 expanded)
%              Number of equality atoms :   39 (  96 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
     => ( k1_mcart_1(X1) = X2
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
       => ( k1_mcart_1(X1) = X2
          & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t12_mcart_1])).

fof(c_0_14,negated_conjecture,
    ( r2_hidden(esk5_0,k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))
    & ( k1_mcart_1(esk5_0) != esk6_0
      | ~ r2_hidden(k2_mcart_1(esk5_0),esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_15,plain,(
    ! [X23] : k2_tarski(X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X26,X27,X28] : k2_enumset1(X26,X26,X27,X28) = k1_enumset1(X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X29,X30,X31,X32] : k3_enumset1(X29,X29,X30,X31,X32) = k2_enumset1(X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_19,plain,(
    ! [X38,X39] :
      ( r2_hidden(X38,X39)
      | r1_xboole_0(k1_tarski(X38),X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_20,plain,(
    ! [X48] : k1_ordinal1(X48) = k2_xboole_0(X48,k1_tarski(X48)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_21,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X9,X8)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X8)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X13)
        | r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k2_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_22,plain,(
    ! [X53,X54,X55] :
      ( ( r2_hidden(k1_mcart_1(X53),X54)
        | ~ r2_hidden(X53,k2_zfmisc_1(X54,X55)) )
      & ( r2_hidden(k2_mcart_1(X53),X55)
        | ~ r2_hidden(X53,k2_zfmisc_1(X54,X55)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk5_0,k2_zfmisc_1(k1_tarski(esk6_0),esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_28,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r2_hidden(esk2_2(X15,X16),X15)
        | r1_xboole_0(X15,X16) )
      & ( r2_hidden(esk2_2(X15,X16),X16)
        | r1_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X49,X50] :
      ( ( ~ r2_hidden(X49,k1_ordinal1(X50))
        | r2_hidden(X49,X50)
        | X49 = X50 )
      & ( ~ r2_hidden(X49,X50)
        | r2_hidden(X49,k1_ordinal1(X50)) )
      & ( X49 != X50
        | r2_hidden(X49,k1_ordinal1(X50)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_31,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk5_0,k2_zfmisc_1(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_35,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_36,plain,(
    ! [X21,X22] :
      ( ( r1_tarski(X21,X22)
        | X21 != X22 )
      & ( r1_tarski(X22,X21)
        | X21 != X22 )
      & ( ~ r1_tarski(X21,X22)
        | ~ r1_tarski(X22,X21)
        | X21 = X22 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_24]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_24])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k1_mcart_1(esk5_0) != esk6_0
    | ~ r2_hidden(k2_mcart_1(esk5_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk5_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

fof(c_0_45,plain,(
    ! [X51,X52] :
      ( ~ r2_hidden(X51,X52)
      | ~ r1_tarski(X52,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k3_enumset1(X1,X1,X1,X1,X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_48,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k3_enumset1(X2,X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk5_0),k2_xboole_0(X1,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k1_mcart_1(esk5_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk6_0,X1)
    | ~ r2_hidden(k1_mcart_1(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:08:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.12/0.36  # and selection function SelectNegativeLiterals.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.017 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t12_mcart_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 0.12/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.36  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.36  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.12/0.36  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.12/0.36  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.12/0.36  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.12/0.36  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.12/0.36  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.12/0.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.36  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.12/0.36  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3)))), inference(assume_negation,[status(cth)],[t12_mcart_1])).
% 0.12/0.36  fof(c_0_14, negated_conjecture, (r2_hidden(esk5_0,k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))&(k1_mcart_1(esk5_0)!=esk6_0|~r2_hidden(k2_mcart_1(esk5_0),esk7_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.12/0.36  fof(c_0_15, plain, ![X23]:k2_tarski(X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.36  fof(c_0_16, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.36  fof(c_0_17, plain, ![X26, X27, X28]:k2_enumset1(X26,X26,X27,X28)=k1_enumset1(X26,X27,X28), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.36  fof(c_0_18, plain, ![X29, X30, X31, X32]:k3_enumset1(X29,X29,X30,X31,X32)=k2_enumset1(X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.36  fof(c_0_19, plain, ![X38, X39]:(r2_hidden(X38,X39)|r1_xboole_0(k1_tarski(X38),X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.12/0.36  fof(c_0_20, plain, ![X48]:k1_ordinal1(X48)=k2_xboole_0(X48,k1_tarski(X48)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.12/0.36  fof(c_0_21, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(r2_hidden(X9,X6)|r2_hidden(X9,X7))|X8!=k2_xboole_0(X6,X7))&((~r2_hidden(X10,X6)|r2_hidden(X10,X8)|X8!=k2_xboole_0(X6,X7))&(~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k2_xboole_0(X6,X7))))&(((~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_xboole_0(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k2_xboole_0(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.12/0.36  fof(c_0_22, plain, ![X53, X54, X55]:((r2_hidden(k1_mcart_1(X53),X54)|~r2_hidden(X53,k2_zfmisc_1(X54,X55)))&(r2_hidden(k2_mcart_1(X53),X55)|~r2_hidden(X53,k2_zfmisc_1(X54,X55)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.12/0.36  cnf(c_0_23, negated_conjecture, (r2_hidden(esk5_0,k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.36  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_27, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  fof(c_0_28, plain, ![X15, X16, X18, X19, X20]:(((r2_hidden(esk2_2(X15,X16),X15)|r1_xboole_0(X15,X16))&(r2_hidden(esk2_2(X15,X16),X16)|r1_xboole_0(X15,X16)))&(~r2_hidden(X20,X18)|~r2_hidden(X20,X19)|~r1_xboole_0(X18,X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.12/0.36  cnf(c_0_29, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.36  fof(c_0_30, plain, ![X49, X50]:((~r2_hidden(X49,k1_ordinal1(X50))|(r2_hidden(X49,X50)|X49=X50))&((~r2_hidden(X49,X50)|r2_hidden(X49,k1_ordinal1(X50)))&(X49!=X50|r2_hidden(X49,k1_ordinal1(X50))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.12/0.36  cnf(c_0_31, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.36  cnf(c_0_32, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.36  cnf(c_0_33, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.36  cnf(c_0_34, negated_conjecture, (r2_hidden(esk5_0,k2_zfmisc_1(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27])).
% 0.12/0.36  cnf(c_0_35, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.36  fof(c_0_36, plain, ![X21, X22]:(((r1_tarski(X21,X22)|X21!=X22)&(r1_tarski(X22,X21)|X21!=X22))&(~r1_tarski(X21,X22)|~r1_tarski(X22,X21)|X21=X22)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.36  cnf(c_0_37, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.36  cnf(c_0_38, plain, (r2_hidden(X1,X2)|r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_24]), c_0_25]), c_0_26]), c_0_27])).
% 0.12/0.36  cnf(c_0_39, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.36  cnf(c_0_40, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_31, c_0_24])).
% 0.12/0.36  cnf(c_0_41, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_32])).
% 0.12/0.36  cnf(c_0_42, negated_conjecture, (r2_hidden(k1_mcart_1(esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.36  cnf(c_0_43, negated_conjecture, (k1_mcart_1(esk5_0)!=esk6_0|~r2_hidden(k2_mcart_1(esk5_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_44, negated_conjecture, (r2_hidden(k2_mcart_1(esk5_0),esk7_0)), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 0.12/0.36  fof(c_0_45, plain, ![X51, X52]:(~r2_hidden(X51,X52)|~r1_tarski(X52,X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.12/0.36  cnf(c_0_46, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.36  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k3_enumset1(X1,X1,X1,X1,X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.36  cnf(c_0_48, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k3_enumset1(X2,X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_25]), c_0_26]), c_0_27])).
% 0.12/0.36  cnf(c_0_49, negated_conjecture, (r2_hidden(k1_mcart_1(esk5_0),k2_xboole_0(X1,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.36  cnf(c_0_50, negated_conjecture, (k1_mcart_1(esk5_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])])).
% 0.12/0.36  cnf(c_0_51, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.12/0.36  cnf(c_0_52, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_46])).
% 0.12/0.36  cnf(c_0_53, negated_conjecture, (r2_hidden(esk6_0,X1)|~r2_hidden(k1_mcart_1(esk5_0),X1)), inference(spm,[status(thm)],[c_0_47, c_0_42])).
% 0.12/0.36  cnf(c_0_54, negated_conjecture, (r2_hidden(k1_mcart_1(esk5_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.12/0.36  cnf(c_0_55, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.12/0.36  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 57
% 0.12/0.36  # Proof object clause steps            : 30
% 0.12/0.36  # Proof object formula steps           : 27
% 0.12/0.36  # Proof object conjectures             : 13
% 0.12/0.36  # Proof object clause conjectures      : 10
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 15
% 0.12/0.36  # Proof object initial formulas used   : 13
% 0.12/0.36  # Proof object generating inferences   : 8
% 0.12/0.36  # Proof object simplifying inferences  : 19
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 17
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 34
% 0.12/0.36  # Removed in clause preprocessing      : 5
% 0.12/0.36  # Initial clauses in saturation        : 29
% 0.12/0.36  # Processed clauses                    : 119
% 0.12/0.36  # ...of these trivial                  : 5
% 0.12/0.36  # ...subsumed                          : 1
% 0.12/0.36  # ...remaining for further processing  : 113
% 0.12/0.36  # Other redundant clauses eliminated   : 6
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 3
% 0.12/0.36  # Generated clauses                    : 331
% 0.12/0.36  # ...of the previous two non-trivial   : 295
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 325
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 6
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 77
% 0.12/0.36  #    Positive orientable unit clauses  : 31
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 2
% 0.12/0.36  #    Non-unit-clauses                  : 44
% 0.12/0.36  # Current number of unprocessed clauses: 230
% 0.12/0.36  # ...number of literals in the above   : 347
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 35
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 179
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 157
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 1
% 0.12/0.36  # Unit Clause-clause subsumption calls : 16
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 7
% 0.12/0.36  # BW rewrite match successes           : 3
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 7478
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.020 s
% 0.12/0.36  # System time              : 0.004 s
% 0.12/0.36  # Total time               : 0.024 s
% 0.12/0.36  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
