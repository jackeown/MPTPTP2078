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
% DateTime   : Thu Dec  3 10:59:08 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 161 expanded)
%              Number of clauses        :   34 (  70 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  157 ( 362 expanded)
%              Number of equality atoms :   45 ( 141 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t15_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & r2_hidden(k2_mcart_1(X1),X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t144_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t13_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & k2_mcart_1(X1) = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))
       => ( ( k1_mcart_1(X1) = X2
            | k1_mcart_1(X1) = X3 )
          & r2_hidden(k2_mcart_1(X1),X4) ) ) ),
    inference(assume_negation,[status(cth)],[t15_mcart_1])).

fof(c_0_13,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_14,plain,(
    ! [X26,X27,X28] :
      ( r2_hidden(X26,X28)
      | r2_hidden(X27,X28)
      | X28 = k4_xboole_0(X28,k2_tarski(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).

fof(c_0_15,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X19,X20,X21] : k2_enumset1(X19,X19,X20,X21) = k1_enumset1(X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),esk5_0))
    & ( k1_mcart_1(esk2_0) != esk3_0
      | ~ r2_hidden(k2_mcart_1(esk2_0),esk5_0) )
    & ( k1_mcart_1(esk2_0) != esk4_0
      | ~ r2_hidden(k2_mcart_1(esk2_0),esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | X2 = k4_xboole_0(X2,k2_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X32,X33,X34] :
      ( ( r2_hidden(k1_mcart_1(X32),X33)
        | ~ r2_hidden(X32,k2_zfmisc_1(X33,X34)) )
      & ( r2_hidden(k2_mcart_1(X32),X34)
        | ~ r2_hidden(X32,k2_zfmisc_1(X33,X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X29,X30,X31] :
      ( ( r2_hidden(X29,X31)
        | ~ r1_tarski(k2_tarski(X29,X30),X31) )
      & ( r2_hidden(X30,X31)
        | ~ r1_tarski(k2_tarski(X29,X30),X31) )
      & ( ~ r2_hidden(X29,X31)
        | ~ r2_hidden(X30,X31)
        | r1_tarski(k2_tarski(X29,X30),X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_25,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( X2 = k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X3))
    | r2_hidden(X3,X2)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_20]),c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X22,X23,X24,X25] :
      ( ( r2_hidden(X22,X24)
        | ~ r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25)) )
      & ( r2_hidden(X23,X25)
        | ~ r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25)) )
      & ( ~ r2_hidden(X22,X24)
        | ~ r2_hidden(X23,X25)
        | r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_33,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X4,k2_enumset1(X1,X1,X1,X3))
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_20]),c_0_21])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X35,X36,X37] :
      ( ( r2_hidden(k1_mcart_1(X35),X36)
        | ~ r2_hidden(X35,k2_zfmisc_1(X36,k1_tarski(X37))) )
      & ( k2_mcart_1(X35) = X37
        | ~ r2_hidden(X35,k2_zfmisc_1(X36,k1_tarski(X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_mcart_1])])])).

fof(c_0_39,plain,(
    ! [X16] : k2_tarski(X16,X16) = k1_tarski(X16) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk4_0,X1)
    | r2_hidden(esk3_0,X1)
    | ~ r2_hidden(k1_mcart_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( k2_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(k2_mcart_1(esk2_0),X1),k2_zfmisc_1(esk5_0,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1))
    | r2_hidden(esk4_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_48,plain,(
    ! [X38,X39] :
      ( k1_mcart_1(k4_tarski(X38,X39)) = X38
      & k2_mcart_1(k4_tarski(X38,X39)) = X39 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_49,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk4_0
    | ~ r2_hidden(k2_mcart_1(esk2_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_50,plain,
    ( k2_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_20]),c_0_21])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k4_tarski(k2_mcart_1(esk2_0),esk4_0),k2_zfmisc_1(esk5_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1)))
    | r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_41])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_55,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk3_0
    | ~ r2_hidden(k2_mcart_1(esk2_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(k4_tarski(k2_mcart_1(esk2_0),esk3_0),k2_zfmisc_1(esk5_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_41])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_56]),c_0_52]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:23:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.65  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.47/0.65  # and selection function SelectNegativeLiterals.
% 0.47/0.65  #
% 0.47/0.65  # Preprocessing time       : 0.027 s
% 0.47/0.65  # Presaturation interreduction done
% 0.47/0.65  
% 0.47/0.65  # Proof found!
% 0.47/0.65  # SZS status Theorem
% 0.47/0.65  # SZS output start CNFRefutation
% 0.47/0.65  fof(t15_mcart_1, conjecture, ![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&r2_hidden(k2_mcart_1(X1),X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 0.47/0.65  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.47/0.65  fof(t144_zfmisc_1, axiom, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 0.47/0.65  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.47/0.65  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.47/0.65  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.47/0.65  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.47/0.65  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.47/0.65  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.47/0.65  fof(t13_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))=>(r2_hidden(k1_mcart_1(X1),X2)&k2_mcart_1(X1)=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_mcart_1)).
% 0.47/0.65  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.47/0.65  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.47/0.65  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&r2_hidden(k2_mcart_1(X1),X4)))), inference(assume_negation,[status(cth)],[t15_mcart_1])).
% 0.47/0.65  fof(c_0_13, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.47/0.65  fof(c_0_14, plain, ![X26, X27, X28]:(r2_hidden(X26,X28)|r2_hidden(X27,X28)|X28=k4_xboole_0(X28,k2_tarski(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).
% 0.47/0.65  fof(c_0_15, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.47/0.65  fof(c_0_16, plain, ![X19, X20, X21]:k2_enumset1(X19,X19,X20,X21)=k1_enumset1(X19,X20,X21), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.47/0.65  fof(c_0_17, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),esk5_0))&((k1_mcart_1(esk2_0)!=esk3_0|~r2_hidden(k2_mcart_1(esk2_0),esk5_0))&(k1_mcart_1(esk2_0)!=esk4_0|~r2_hidden(k2_mcart_1(esk2_0),esk5_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.47/0.65  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.65  cnf(c_0_19, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|X2=k4_xboole_0(X2,k2_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.65  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.47/0.65  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.47/0.65  fof(c_0_22, plain, ![X32, X33, X34]:((r2_hidden(k1_mcart_1(X32),X33)|~r2_hidden(X32,k2_zfmisc_1(X33,X34)))&(r2_hidden(k2_mcart_1(X32),X34)|~r2_hidden(X32,k2_zfmisc_1(X33,X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.47/0.65  cnf(c_0_23, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),esk5_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.65  fof(c_0_24, plain, ![X29, X30, X31]:(((r2_hidden(X29,X31)|~r1_tarski(k2_tarski(X29,X30),X31))&(r2_hidden(X30,X31)|~r1_tarski(k2_tarski(X29,X30),X31)))&(~r2_hidden(X29,X31)|~r2_hidden(X30,X31)|r1_tarski(k2_tarski(X29,X30),X31))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.47/0.65  fof(c_0_25, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.47/0.65  cnf(c_0_26, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_18])).
% 0.47/0.65  cnf(c_0_27, plain, (X2=k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X3))|r2_hidden(X3,X2)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.47/0.65  cnf(c_0_28, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.47/0.65  cnf(c_0_29, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_20]), c_0_21])).
% 0.47/0.65  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.47/0.65  cnf(c_0_31, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.47/0.65  fof(c_0_32, plain, ![X22, X23, X24, X25]:(((r2_hidden(X22,X24)|~r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25)))&(r2_hidden(X23,X25)|~r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25))))&(~r2_hidden(X22,X24)|~r2_hidden(X23,X25)|r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.47/0.65  cnf(c_0_33, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.47/0.65  cnf(c_0_34, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|~r2_hidden(X4,k2_enumset1(X1,X1,X1,X3))|~r2_hidden(X4,X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.47/0.65  cnf(c_0_35, negated_conjecture, (r2_hidden(k1_mcart_1(esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.47/0.65  cnf(c_0_36, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_20]), c_0_21])).
% 0.47/0.65  cnf(c_0_37, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_31])).
% 0.47/0.65  fof(c_0_38, plain, ![X35, X36, X37]:((r2_hidden(k1_mcart_1(X35),X36)|~r2_hidden(X35,k2_zfmisc_1(X36,k1_tarski(X37))))&(k2_mcart_1(X35)=X37|~r2_hidden(X35,k2_zfmisc_1(X36,k1_tarski(X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_mcart_1])])])).
% 0.47/0.65  fof(c_0_39, plain, ![X16]:k2_tarski(X16,X16)=k1_tarski(X16), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.47/0.65  cnf(c_0_40, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.47/0.65  cnf(c_0_41, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_29])).
% 0.47/0.65  cnf(c_0_42, negated_conjecture, (r2_hidden(esk4_0,X1)|r2_hidden(esk3_0,X1)|~r2_hidden(k1_mcart_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.47/0.65  cnf(c_0_43, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.47/0.65  cnf(c_0_44, plain, (k2_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.47/0.65  cnf(c_0_45, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.47/0.65  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_tarski(k2_mcart_1(esk2_0),X1),k2_zfmisc_1(esk5_0,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.47/0.65  cnf(c_0_47, negated_conjecture, (r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1))|r2_hidden(esk4_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.47/0.65  fof(c_0_48, plain, ![X38, X39]:(k1_mcart_1(k4_tarski(X38,X39))=X38&k2_mcart_1(k4_tarski(X38,X39))=X39), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.47/0.65  cnf(c_0_49, negated_conjecture, (k1_mcart_1(esk2_0)!=esk4_0|~r2_hidden(k2_mcart_1(esk2_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.65  cnf(c_0_50, plain, (k2_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(X3,k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_20]), c_0_21])).
% 0.47/0.65  cnf(c_0_51, negated_conjecture, (r2_hidden(k4_tarski(k2_mcart_1(esk2_0),esk4_0),k2_zfmisc_1(esk5_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1)))|r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.47/0.65  cnf(c_0_52, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.47/0.65  cnf(c_0_53, negated_conjecture, (k1_mcart_1(esk2_0)!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_41])])).
% 0.47/0.65  cnf(c_0_54, negated_conjecture, (r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0)))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53])).
% 0.47/0.65  cnf(c_0_55, negated_conjecture, (k1_mcart_1(esk2_0)!=esk3_0|~r2_hidden(k2_mcart_1(esk2_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.65  cnf(c_0_56, negated_conjecture, (r2_hidden(k4_tarski(k2_mcart_1(esk2_0),esk3_0),k2_zfmisc_1(esk5_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0))))), inference(spm,[status(thm)],[c_0_46, c_0_54])).
% 0.47/0.65  cnf(c_0_57, negated_conjecture, (k1_mcart_1(esk2_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_41])])).
% 0.47/0.65  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_56]), c_0_52]), c_0_57]), ['proof']).
% 0.47/0.65  # SZS output end CNFRefutation
% 0.47/0.65  # Proof object total steps             : 59
% 0.47/0.65  # Proof object clause steps            : 34
% 0.47/0.65  # Proof object formula steps           : 25
% 0.47/0.65  # Proof object conjectures             : 18
% 0.47/0.65  # Proof object clause conjectures      : 15
% 0.47/0.65  # Proof object formula conjectures     : 3
% 0.47/0.65  # Proof object initial clauses used    : 15
% 0.47/0.65  # Proof object initial formulas used   : 12
% 0.47/0.65  # Proof object generating inferences   : 11
% 0.47/0.65  # Proof object simplifying inferences  : 19
% 0.47/0.65  # Training examples: 0 positive, 0 negative
% 0.47/0.65  # Parsed axioms                        : 12
% 0.47/0.65  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.65  # Initial clauses                      : 28
% 0.47/0.65  # Removed in clause preprocessing      : 3
% 0.47/0.65  # Initial clauses in saturation        : 25
% 0.47/0.65  # Processed clauses                    : 409
% 0.47/0.65  # ...of these trivial                  : 22
% 0.47/0.65  # ...subsumed                          : 48
% 0.47/0.65  # ...remaining for further processing  : 339
% 0.47/0.65  # Other redundant clauses eliminated   : 25
% 0.47/0.65  # Clauses deleted for lack of memory   : 0
% 0.47/0.65  # Backward-subsumed                    : 1
% 0.47/0.65  # Backward-rewritten                   : 3
% 0.47/0.65  # Generated clauses                    : 21310
% 0.47/0.65  # ...of the previous two non-trivial   : 20685
% 0.47/0.65  # Contextual simplify-reflections      : 0
% 0.47/0.65  # Paramodulations                      : 21275
% 0.47/0.65  # Factorizations                       : 10
% 0.47/0.65  # Equation resolutions                 : 25
% 0.47/0.65  # Propositional unsat checks           : 0
% 0.47/0.65  #    Propositional check models        : 0
% 0.47/0.65  #    Propositional check unsatisfiable : 0
% 0.47/0.65  #    Propositional clauses             : 0
% 0.47/0.65  #    Propositional clauses after purity: 0
% 0.47/0.65  #    Propositional unsat core size     : 0
% 0.47/0.65  #    Propositional preprocessing time  : 0.000
% 0.47/0.65  #    Propositional encoding time       : 0.000
% 0.47/0.65  #    Propositional solver time         : 0.000
% 0.47/0.65  #    Success case prop preproc time    : 0.000
% 0.47/0.65  #    Success case prop encoding time   : 0.000
% 0.47/0.65  #    Success case prop solver time     : 0.000
% 0.47/0.65  # Current number of processed clauses  : 307
% 0.47/0.65  #    Positive orientable unit clauses  : 114
% 0.47/0.65  #    Positive unorientable unit clauses: 0
% 0.47/0.65  #    Negative unit clauses             : 2
% 0.47/0.65  #    Non-unit-clauses                  : 191
% 0.47/0.65  # Current number of unprocessed clauses: 20247
% 0.47/0.65  # ...number of literals in the above   : 70055
% 0.47/0.65  # Current number of archived formulas  : 0
% 0.47/0.65  # Current number of archived clauses   : 30
% 0.47/0.65  # Clause-clause subsumption calls (NU) : 2497
% 0.47/0.65  # Rec. Clause-clause subsumption calls : 2003
% 0.47/0.65  # Non-unit clause-clause subsumptions  : 49
% 0.47/0.65  # Unit Clause-clause subsumption calls : 59
% 0.47/0.65  # Rewrite failures with RHS unbound    : 0
% 0.47/0.65  # BW rewrite match attempts            : 344
% 0.47/0.65  # BW rewrite match successes           : 2
% 0.47/0.65  # Condensation attempts                : 0
% 0.47/0.65  # Condensation successes               : 0
% 0.47/0.65  # Termbank termtop insertions          : 606644
% 0.47/0.66  
% 0.47/0.66  # -------------------------------------------------
% 0.47/0.66  # User time                : 0.294 s
% 0.47/0.66  # System time              : 0.024 s
% 0.47/0.66  # Total time               : 0.318 s
% 0.47/0.66  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
