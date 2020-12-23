%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:20 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 185 expanded)
%              Number of clauses        :   49 (  87 expanded)
%              Number of leaves         :   13 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  191 ( 514 expanded)
%              Number of equality atoms :  115 ( 334 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

fof(c_0_14,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X35,X36] :
      ( ( ~ m1_subset_1(X35,k1_zfmisc_1(X36))
        | r1_tarski(X35,X36) )
      & ( ~ r1_tarski(X35,X36)
        | m1_subset_1(X35,k1_zfmisc_1(X36)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_19,plain,(
    ! [X33] : m1_subset_1(esk3_1(X33),X33) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_20,plain,(
    ! [X27,X28,X29,X30] :
      ( ( r2_hidden(X27,X29)
        | ~ r2_hidden(k4_tarski(X27,X28),k2_zfmisc_1(X29,X30)) )
      & ( r2_hidden(X28,X30)
        | ~ r2_hidden(k4_tarski(X27,X28),k2_zfmisc_1(X29,X30)) )
      & ( ~ r2_hidden(X27,X29)
        | ~ r2_hidden(X28,X30)
        | r2_hidden(k4_tarski(X27,X28),k2_zfmisc_1(X29,X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_21,negated_conjecture,
    ( esk7_0 = k4_tarski(esk8_0,esk9_0)
    & ( esk7_0 = k1_mcart_1(esk7_0)
      | esk7_0 = k2_mcart_1(esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_22,plain,(
    ! [X31,X32] :
      ( ( k2_zfmisc_1(X31,X32) != k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0 )
      & ( X31 != k1_xboole_0
        | k2_zfmisc_1(X31,X32) = k1_xboole_0 )
      & ( X32 != k1_xboole_0
        | k2_zfmisc_1(X31,X32) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_23,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
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

fof(c_0_27,plain,(
    ! [X37,X38] :
      ( ~ r2_hidden(X37,X38)
      | ~ r1_tarski(X38,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( esk7_0 = k4_tarski(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_33,plain,(
    ! [X48,X49] :
      ( k1_mcart_1(k4_tarski(X48,X49)) = X48
      & k2_mcart_1(k4_tarski(X48,X49)) = X49 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_34,plain,(
    ! [X50,X52,X53] :
      ( ( r2_hidden(esk6_1(X50),X50)
        | X50 = k1_xboole_0 )
      & ( ~ r2_hidden(X52,X50)
        | esk6_1(X50) != k4_tarski(X52,X53)
        | X50 = k1_xboole_0 )
      & ( ~ r2_hidden(X53,X50)
        | esk6_1(X50) != k4_tarski(X52,X53)
        | X50 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

cnf(c_0_35,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( r1_tarski(esk3_1(k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk9_0,X1)
    | ~ r2_hidden(esk7_0,k2_zfmisc_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_32])).

fof(c_0_40,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X12
        | X15 = X13
        | X14 != k2_tarski(X12,X13) )
      & ( X16 != X12
        | r2_hidden(X16,X14)
        | X14 != k2_tarski(X12,X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k2_tarski(X12,X13) )
      & ( esk2_3(X17,X18,X19) != X17
        | ~ r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k2_tarski(X17,X18) )
      & ( esk2_3(X17,X18,X19) != X18
        | ~ r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k2_tarski(X17,X18) )
      & ( r2_hidden(esk2_3(X17,X18,X19),X19)
        | esk2_3(X17,X18,X19) = X17
        | esk2_3(X17,X18,X19) = X18
        | X19 = k2_tarski(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_41,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk6_1(X2) != k4_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( r2_hidden(esk6_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,esk3_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk9_0,X1)
    | ~ r2_hidden(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( esk7_0 = k1_mcart_1(esk7_0)
    | esk7_0 = k2_mcart_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_50,negated_conjecture,
    ( k1_mcart_1(esk7_0) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_31])).

cnf(c_0_51,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | k4_tarski(esk6_1(X1),X2) != esk6_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_54,plain,
    ( esk6_1(k2_enumset1(X1,X1,X1,X1)) = X1
    | k2_enumset1(X1,X1,X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_55,plain,
    ( r2_hidden(k4_tarski(X1,X2),k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_45,c_0_39])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_25]),c_0_26])).

cnf(c_0_58,negated_conjecture,
    ( k2_mcart_1(esk7_0) = esk7_0
    | esk8_0 = esk7_0 ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( k2_mcart_1(esk7_0) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_31])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_25]),c_0_26])).

cnf(c_0_61,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | k4_tarski(X1,X2) != X1 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k1_xboole_0)
    | ~ r2_hidden(esk9_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_31]),c_0_56])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_57])])).

cnf(c_0_64,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk6_1(X2) != k4_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_65,negated_conjecture,
    ( esk8_0 = esk7_0
    | esk9_0 = esk7_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_60])])).

cnf(c_0_67,negated_conjecture,
    ( k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0) = k1_xboole_0
    | esk8_0 != esk7_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_31])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,plain,
    ( X1 = k1_xboole_0
    | k4_tarski(X2,esk6_1(X1)) != esk6_1(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_43])).

cnf(c_0_70,negated_conjecture,
    ( k4_tarski(esk8_0,esk7_0) = esk7_0
    | esk8_0 = esk7_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( esk8_0 != esk7_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_72,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | k4_tarski(X2,X1) != X1 ),
    inference(spm,[status(thm)],[c_0_69,c_0_54])).

cnf(c_0_73,negated_conjecture,
    ( k4_tarski(esk8_0,esk7_0) = esk7_0 ),
    inference(sr,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_74]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:16:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 3.90/4.08  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 3.90/4.08  # and selection function PSelectComplexExceptUniqMaxHorn.
% 3.90/4.08  #
% 3.90/4.08  # Preprocessing time       : 0.029 s
% 3.90/4.08  # Presaturation interreduction done
% 3.90/4.08  
% 3.90/4.08  # Proof found!
% 3.90/4.08  # SZS status Theorem
% 3.90/4.08  # SZS output start CNFRefutation
% 3.90/4.08  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.90/4.08  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.90/4.08  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.90/4.08  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.90/4.08  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.90/4.08  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.90/4.08  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.90/4.08  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.90/4.08  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.90/4.08  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.90/4.08  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.90/4.08  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.90/4.08  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.90/4.08  fof(c_0_13, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 3.90/4.08  fof(c_0_14, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 3.90/4.08  fof(c_0_15, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 3.90/4.08  fof(c_0_16, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 3.90/4.08  fof(c_0_17, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 3.90/4.08  fof(c_0_18, plain, ![X35, X36]:((~m1_subset_1(X35,k1_zfmisc_1(X36))|r1_tarski(X35,X36))&(~r1_tarski(X35,X36)|m1_subset_1(X35,k1_zfmisc_1(X36)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 3.90/4.08  fof(c_0_19, plain, ![X33]:m1_subset_1(esk3_1(X33),X33), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 3.90/4.08  fof(c_0_20, plain, ![X27, X28, X29, X30]:(((r2_hidden(X27,X29)|~r2_hidden(k4_tarski(X27,X28),k2_zfmisc_1(X29,X30)))&(r2_hidden(X28,X30)|~r2_hidden(k4_tarski(X27,X28),k2_zfmisc_1(X29,X30))))&(~r2_hidden(X27,X29)|~r2_hidden(X28,X30)|r2_hidden(k4_tarski(X27,X28),k2_zfmisc_1(X29,X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 3.90/4.08  fof(c_0_21, negated_conjecture, (esk7_0=k4_tarski(esk8_0,esk9_0)&(esk7_0=k1_mcart_1(esk7_0)|esk7_0=k2_mcart_1(esk7_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 3.90/4.08  fof(c_0_22, plain, ![X31, X32]:((k2_zfmisc_1(X31,X32)!=k1_xboole_0|(X31=k1_xboole_0|X32=k1_xboole_0))&((X31!=k1_xboole_0|k2_zfmisc_1(X31,X32)=k1_xboole_0)&(X32!=k1_xboole_0|k2_zfmisc_1(X31,X32)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 3.90/4.08  cnf(c_0_23, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.90/4.08  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.90/4.08  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.90/4.08  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.90/4.08  fof(c_0_27, plain, ![X37, X38]:(~r2_hidden(X37,X38)|~r1_tarski(X38,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 3.90/4.08  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.90/4.08  cnf(c_0_29, plain, (m1_subset_1(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.90/4.08  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.90/4.08  cnf(c_0_31, negated_conjecture, (esk7_0=k4_tarski(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.90/4.08  cnf(c_0_32, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.90/4.08  fof(c_0_33, plain, ![X48, X49]:(k1_mcart_1(k4_tarski(X48,X49))=X48&k2_mcart_1(k4_tarski(X48,X49))=X49), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 3.90/4.08  fof(c_0_34, plain, ![X50, X52, X53]:((r2_hidden(esk6_1(X50),X50)|X50=k1_xboole_0)&((~r2_hidden(X52,X50)|esk6_1(X50)!=k4_tarski(X52,X53)|X50=k1_xboole_0)&(~r2_hidden(X53,X50)|esk6_1(X50)!=k4_tarski(X52,X53)|X50=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 3.90/4.08  cnf(c_0_35, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])).
% 3.90/4.08  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.90/4.08  cnf(c_0_37, plain, (r1_tarski(esk3_1(k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 3.90/4.08  cnf(c_0_38, negated_conjecture, (r2_hidden(esk9_0,X1)|~r2_hidden(esk7_0,k2_zfmisc_1(X2,X1))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 3.90/4.08  cnf(c_0_39, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_32])).
% 3.90/4.08  fof(c_0_40, plain, ![X12, X13, X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X15,X14)|(X15=X12|X15=X13)|X14!=k2_tarski(X12,X13))&((X16!=X12|r2_hidden(X16,X14)|X14!=k2_tarski(X12,X13))&(X16!=X13|r2_hidden(X16,X14)|X14!=k2_tarski(X12,X13))))&(((esk2_3(X17,X18,X19)!=X17|~r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k2_tarski(X17,X18))&(esk2_3(X17,X18,X19)!=X18|~r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k2_tarski(X17,X18)))&(r2_hidden(esk2_3(X17,X18,X19),X19)|(esk2_3(X17,X18,X19)=X17|esk2_3(X17,X18,X19)=X18)|X19=k2_tarski(X17,X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 3.90/4.08  cnf(c_0_41, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 3.90/4.08  cnf(c_0_42, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk6_1(X2)!=k4_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 3.90/4.08  cnf(c_0_43, plain, (r2_hidden(esk6_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 3.90/4.08  cnf(c_0_44, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_35])).
% 3.90/4.08  cnf(c_0_45, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.90/4.08  cnf(c_0_46, plain, (~r2_hidden(X1,esk3_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 3.90/4.08  cnf(c_0_47, negated_conjecture, (r2_hidden(esk9_0,X1)|~r2_hidden(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 3.90/4.08  cnf(c_0_48, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 3.90/4.08  cnf(c_0_49, negated_conjecture, (esk7_0=k1_mcart_1(esk7_0)|esk7_0=k2_mcart_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.90/4.08  cnf(c_0_50, negated_conjecture, (k1_mcart_1(esk7_0)=esk8_0), inference(spm,[status(thm)],[c_0_41, c_0_31])).
% 3.90/4.08  cnf(c_0_51, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_33])).
% 3.90/4.08  cnf(c_0_52, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 3.90/4.08  cnf(c_0_53, plain, (X1=k1_xboole_0|k4_tarski(esk6_1(X1),X2)!=esk6_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 3.90/4.08  cnf(c_0_54, plain, (esk6_1(k2_enumset1(X1,X1,X1,X1))=X1|k2_enumset1(X1,X1,X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_43])).
% 3.90/4.08  cnf(c_0_55, plain, (r2_hidden(k4_tarski(X1,X2),k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_45, c_0_39])).
% 3.90/4.08  cnf(c_0_56, negated_conjecture, (~r2_hidden(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 3.90/4.08  cnf(c_0_57, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_25]), c_0_26])).
% 3.90/4.08  cnf(c_0_58, negated_conjecture, (k2_mcart_1(esk7_0)=esk7_0|esk8_0=esk7_0), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 3.90/4.08  cnf(c_0_59, negated_conjecture, (k2_mcart_1(esk7_0)=esk9_0), inference(spm,[status(thm)],[c_0_51, c_0_31])).
% 3.90/4.08  cnf(c_0_60, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_25]), c_0_26])).
% 3.90/4.08  cnf(c_0_61, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|k4_tarski(X1,X2)!=X1), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 3.90/4.08  cnf(c_0_62, negated_conjecture, (~r2_hidden(esk8_0,k1_xboole_0)|~r2_hidden(esk9_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_31]), c_0_56])).
% 3.90/4.08  cnf(c_0_63, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_57])])).
% 3.90/4.08  cnf(c_0_64, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk6_1(X2)!=k4_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 3.90/4.08  cnf(c_0_65, negated_conjecture, (esk8_0=esk7_0|esk9_0=esk7_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 3.90/4.08  cnf(c_0_66, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_60])])).
% 3.90/4.08  cnf(c_0_67, negated_conjecture, (k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)=k1_xboole_0|esk8_0!=esk7_0), inference(spm,[status(thm)],[c_0_61, c_0_31])).
% 3.90/4.08  cnf(c_0_68, negated_conjecture, (~r2_hidden(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 3.90/4.08  cnf(c_0_69, plain, (X1=k1_xboole_0|k4_tarski(X2,esk6_1(X1))!=esk6_1(X1)), inference(spm,[status(thm)],[c_0_64, c_0_43])).
% 3.90/4.08  cnf(c_0_70, negated_conjecture, (k4_tarski(esk8_0,esk7_0)=esk7_0|esk8_0=esk7_0), inference(spm,[status(thm)],[c_0_31, c_0_65])).
% 3.90/4.08  cnf(c_0_71, negated_conjecture, (esk8_0!=esk7_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 3.90/4.08  cnf(c_0_72, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|k4_tarski(X2,X1)!=X1), inference(spm,[status(thm)],[c_0_69, c_0_54])).
% 3.90/4.08  cnf(c_0_73, negated_conjecture, (k4_tarski(esk8_0,esk7_0)=esk7_0), inference(sr,[status(thm)],[c_0_70, c_0_71])).
% 3.90/4.08  cnf(c_0_74, negated_conjecture, (k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 3.90/4.08  cnf(c_0_75, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_74]), c_0_56]), ['proof']).
% 3.90/4.08  # SZS output end CNFRefutation
% 3.90/4.08  # Proof object total steps             : 76
% 3.90/4.08  # Proof object clause steps            : 49
% 3.90/4.08  # Proof object formula steps           : 27
% 3.90/4.08  # Proof object conjectures             : 20
% 3.90/4.08  # Proof object clause conjectures      : 17
% 3.90/4.08  # Proof object formula conjectures     : 3
% 3.90/4.08  # Proof object initial clauses used    : 19
% 3.90/4.08  # Proof object initial formulas used   : 13
% 3.90/4.08  # Proof object generating inferences   : 21
% 3.90/4.08  # Proof object simplifying inferences  : 18
% 3.90/4.08  # Training examples: 0 positive, 0 negative
% 3.90/4.08  # Parsed axioms                        : 14
% 3.90/4.08  # Removed by relevancy pruning/SinE    : 0
% 3.90/4.08  # Initial clauses                      : 33
% 3.90/4.08  # Removed in clause preprocessing      : 3
% 3.90/4.08  # Initial clauses in saturation        : 30
% 3.90/4.08  # Processed clauses                    : 4979
% 3.90/4.08  # ...of these trivial                  : 44
% 3.90/4.08  # ...subsumed                          : 4033
% 3.90/4.08  # ...remaining for further processing  : 902
% 3.90/4.08  # Other redundant clauses eliminated   : 5148
% 3.90/4.08  # Clauses deleted for lack of memory   : 0
% 3.90/4.08  # Backward-subsumed                    : 107
% 3.90/4.08  # Backward-rewritten                   : 206
% 3.90/4.08  # Generated clauses                    : 210374
% 3.90/4.08  # ...of the previous two non-trivial   : 201758
% 3.90/4.08  # Contextual simplify-reflections      : 14
% 3.90/4.08  # Paramodulations                      : 204720
% 3.90/4.08  # Factorizations                       : 440
% 3.90/4.08  # Equation resolutions                 : 5150
% 3.90/4.08  # Propositional unsat checks           : 0
% 3.90/4.08  #    Propositional check models        : 0
% 3.90/4.08  #    Propositional check unsatisfiable : 0
% 3.90/4.08  #    Propositional clauses             : 0
% 3.90/4.08  #    Propositional clauses after purity: 0
% 3.90/4.08  #    Propositional unsat core size     : 0
% 3.90/4.08  #    Propositional preprocessing time  : 0.000
% 3.90/4.08  #    Propositional encoding time       : 0.000
% 3.90/4.08  #    Propositional solver time         : 0.000
% 3.90/4.08  #    Success case prop preproc time    : 0.000
% 3.90/4.08  #    Success case prop encoding time   : 0.000
% 3.90/4.08  #    Success case prop solver time     : 0.000
% 3.90/4.08  # Current number of processed clauses  : 482
% 3.90/4.08  #    Positive orientable unit clauses  : 16
% 3.90/4.08  #    Positive unorientable unit clauses: 0
% 3.90/4.08  #    Negative unit clauses             : 4
% 3.90/4.08  #    Non-unit-clauses                  : 462
% 3.90/4.08  # Current number of unprocessed clauses: 193155
% 3.90/4.08  # ...number of literals in the above   : 1668062
% 3.90/4.08  # Current number of archived formulas  : 0
% 3.90/4.08  # Current number of archived clauses   : 413
% 3.90/4.08  # Clause-clause subsumption calls (NU) : 137610
% 3.90/4.08  # Rec. Clause-clause subsumption calls : 31497
% 3.90/4.08  # Non-unit clause-clause subsumptions  : 3302
% 3.90/4.08  # Unit Clause-clause subsumption calls : 1001
% 3.90/4.08  # Rewrite failures with RHS unbound    : 0
% 3.90/4.08  # BW rewrite match attempts            : 14
% 3.90/4.08  # BW rewrite match successes           : 7
% 3.90/4.08  # Condensation attempts                : 0
% 3.90/4.08  # Condensation successes               : 0
% 3.90/4.08  # Termbank termtop insertions          : 5672341
% 3.90/4.09  
% 3.90/4.09  # -------------------------------------------------
% 3.90/4.09  # User time                : 3.627 s
% 3.90/4.09  # System time              : 0.113 s
% 3.90/4.09  # Total time               : 3.741 s
% 3.90/4.09  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
