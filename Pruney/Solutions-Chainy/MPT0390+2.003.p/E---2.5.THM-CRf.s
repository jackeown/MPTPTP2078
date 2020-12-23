%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:06 EST 2020

% Result     : Theorem 0.68s
% Output     : CNFRefutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 182 expanded)
%              Number of clauses        :   56 (  93 expanded)
%              Number of leaves         :   10 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  259 ( 751 expanded)
%              Number of equality atoms :   59 ( 137 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t8_setfam_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(k1_setfam_1(X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(c_0_10,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( r2_hidden(X23,X20)
        | ~ r2_hidden(X23,X22)
        | X22 != k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | X22 != k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X20)
        | r2_hidden(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk3_3(X25,X26,X27),X27)
        | ~ r2_hidden(esk3_3(X25,X26,X27),X25)
        | r2_hidden(esk3_3(X25,X26,X27),X26)
        | X27 = k4_xboole_0(X25,X26) )
      & ( r2_hidden(esk3_3(X25,X26,X27),X25)
        | r2_hidden(esk3_3(X25,X26,X27),X27)
        | X27 = k4_xboole_0(X25,X26) )
      & ( ~ r2_hidden(esk3_3(X25,X26,X27),X26)
        | r2_hidden(esk3_3(X25,X26,X27),X27)
        | X27 = k4_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_11,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X41,X42,X44] :
      ( ( r2_hidden(esk4_2(X41,X42),X42)
        | ~ r2_hidden(X41,X42) )
      & ( ~ r2_hidden(X44,X42)
        | ~ r2_hidden(X44,esk4_2(X41,X42))
        | ~ r2_hidden(X41,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X29,X30,X31] :
      ( ~ r1_tarski(k2_xboole_0(X29,X30),X31)
      | r1_tarski(X29,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_19,plain,(
    ! [X32,X33] :
      ( ~ r1_tarski(X32,X33)
      | k2_xboole_0(X32,X33) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r2_hidden(X1,X2)
          & r1_tarski(X1,X3) )
       => r1_tarski(k1_setfam_1(X2),X3) ) ),
    inference(assume_negation,[status(cth)],[t8_setfam_1])).

fof(c_0_21,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_22,plain,(
    ! [X34,X35] :
      ( ~ r1_tarski(X34,X35)
      | k3_xboole_0(X34,X35) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r2_hidden(esk4_2(X1,k4_xboole_0(X2,X3)),X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,negated_conjecture,
    ( r2_hidden(esk8_0,esk9_0)
    & r1_tarski(esk8_0,esk10_0)
    & ~ r1_tarski(k1_setfam_1(esk9_0),esk10_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,plain,(
    ! [X45,X46,X47,X48,X49,X51,X54,X55,X56,X57] :
      ( ( ~ r2_hidden(X47,X46)
        | ~ r2_hidden(X48,X45)
        | r2_hidden(X47,X48)
        | X46 != k1_setfam_1(X45)
        | X45 = k1_xboole_0 )
      & ( r2_hidden(esk5_3(X45,X46,X49),X45)
        | r2_hidden(X49,X46)
        | X46 != k1_setfam_1(X45)
        | X45 = k1_xboole_0 )
      & ( ~ r2_hidden(X49,esk5_3(X45,X46,X49))
        | r2_hidden(X49,X46)
        | X46 != k1_setfam_1(X45)
        | X45 = k1_xboole_0 )
      & ( r2_hidden(esk7_2(X45,X51),X45)
        | ~ r2_hidden(esk6_2(X45,X51),X51)
        | X51 = k1_setfam_1(X45)
        | X45 = k1_xboole_0 )
      & ( ~ r2_hidden(esk6_2(X45,X51),esk7_2(X45,X51))
        | ~ r2_hidden(esk6_2(X45,X51),X51)
        | X51 = k1_setfam_1(X45)
        | X45 = k1_xboole_0 )
      & ( r2_hidden(esk6_2(X45,X51),X51)
        | ~ r2_hidden(X54,X45)
        | r2_hidden(esk6_2(X45,X51),X54)
        | X51 = k1_setfam_1(X45)
        | X45 = k1_xboole_0 )
      & ( X56 != k1_setfam_1(X55)
        | X56 = k1_xboole_0
        | X55 != k1_xboole_0 )
      & ( X57 != k1_xboole_0
        | X57 = k1_setfam_1(X55)
        | X55 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

fof(c_0_32,plain,(
    ! [X36,X37] :
      ( ( k4_xboole_0(X36,X37) != k1_xboole_0
        | r1_tarski(X36,X37) )
      & ( ~ r1_tarski(X36,X37)
        | k4_xboole_0(X36,X37) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(esk4_2(X1,k4_xboole_0(X2,X3)),X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_17])).

cnf(c_0_35,plain,
    ( r2_hidden(esk4_2(X1,k4_xboole_0(k3_xboole_0(X2,X3),X4)),X3)
    | ~ r2_hidden(X1,k4_xboole_0(k3_xboole_0(X2,X3),X4)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk8_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_30])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_33])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k3_xboole_0(X2,X3),X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_46,plain,
    ( r2_hidden(esk4_2(X1,X2),k4_xboole_0(X2,X3))
    | r2_hidden(esk4_2(X1,X2),X3)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(X1,esk10_0)
    | ~ r1_tarski(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_50,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_43])).

cnf(c_0_53,plain,
    ( r2_hidden(esk4_2(X1,X2),X3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_17])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_45,c_0_33])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),k4_xboole_0(esk9_0,X1))
    | r2_hidden(esk4_2(esk8_0,esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X3)
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_48])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_30])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk8_0,X1),esk10_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(k1_setfam_1(X1),X2),X3)
    | r1_tarski(k1_setfam_1(X1),X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_30])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(esk4_2(X1,k1_xboole_0),X2)
    | ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_17])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),X1)
    | ~ r1_tarski(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k3_xboole_0(X3,X1))
    | ~ r2_hidden(esk1_2(k4_xboole_0(X1,X2),k3_xboole_0(X3,X1)),X3) ),
    inference(spm,[status(thm)],[c_0_56,c_0_41])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk1_2(k4_xboole_0(esk8_0,X1),X2),esk10_0)
    | r1_tarski(k4_xboole_0(esk8_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r2_hidden(esk1_2(k1_setfam_1(esk9_0),X1),esk8_0)
    | r1_tarski(k1_setfam_1(esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_47])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_17])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_tarski(esk9_0,k4_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk8_0,X1),k3_xboole_0(esk10_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r1_tarski(k1_setfam_1(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(esk9_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_30])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_30])).

cnf(c_0_73,negated_conjecture,
    ( ~ r1_tarski(esk9_0,k4_xboole_0(esk8_0,k3_xboole_0(esk10_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_69]),c_0_70])).

cnf(c_0_75,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74]),c_0_75])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:57:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.68/0.86  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.68/0.86  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.68/0.86  #
% 0.68/0.86  # Preprocessing time       : 0.029 s
% 0.68/0.86  # Presaturation interreduction done
% 0.68/0.86  
% 0.68/0.86  # Proof found!
% 0.68/0.86  # SZS status Theorem
% 0.68/0.86  # SZS output start CNFRefutation
% 0.68/0.86  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.68/0.86  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.68/0.86  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 0.68/0.86  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.68/0.86  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.68/0.86  fof(t8_setfam_1, conjecture, ![X1, X2, X3]:((r2_hidden(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(k1_setfam_1(X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_setfam_1)).
% 0.68/0.86  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.68/0.86  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.68/0.86  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.68/0.86  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 0.68/0.86  fof(c_0_10, plain, ![X20, X21, X22, X23, X24, X25, X26, X27]:((((r2_hidden(X23,X20)|~r2_hidden(X23,X22)|X22!=k4_xboole_0(X20,X21))&(~r2_hidden(X23,X21)|~r2_hidden(X23,X22)|X22!=k4_xboole_0(X20,X21)))&(~r2_hidden(X24,X20)|r2_hidden(X24,X21)|r2_hidden(X24,X22)|X22!=k4_xboole_0(X20,X21)))&((~r2_hidden(esk3_3(X25,X26,X27),X27)|(~r2_hidden(esk3_3(X25,X26,X27),X25)|r2_hidden(esk3_3(X25,X26,X27),X26))|X27=k4_xboole_0(X25,X26))&((r2_hidden(esk3_3(X25,X26,X27),X25)|r2_hidden(esk3_3(X25,X26,X27),X27)|X27=k4_xboole_0(X25,X26))&(~r2_hidden(esk3_3(X25,X26,X27),X26)|r2_hidden(esk3_3(X25,X26,X27),X27)|X27=k4_xboole_0(X25,X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.68/0.86  fof(c_0_11, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.68/0.86  cnf(c_0_12, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.68/0.86  fof(c_0_13, plain, ![X41, X42, X44]:((r2_hidden(esk4_2(X41,X42),X42)|~r2_hidden(X41,X42))&(~r2_hidden(X44,X42)|~r2_hidden(X44,esk4_2(X41,X42))|~r2_hidden(X41,X42))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 0.68/0.86  cnf(c_0_14, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.68/0.86  cnf(c_0_15, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.68/0.86  cnf(c_0_16, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_12])).
% 0.68/0.86  cnf(c_0_17, plain, (r2_hidden(esk4_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.68/0.86  fof(c_0_18, plain, ![X29, X30, X31]:(~r1_tarski(k2_xboole_0(X29,X30),X31)|r1_tarski(X29,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.68/0.86  fof(c_0_19, plain, ![X32, X33]:(~r1_tarski(X32,X33)|k2_xboole_0(X32,X33)=X33), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.68/0.86  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:((r2_hidden(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(k1_setfam_1(X2),X3))), inference(assume_negation,[status(cth)],[t8_setfam_1])).
% 0.68/0.86  fof(c_0_21, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.68/0.86  fof(c_0_22, plain, ![X34, X35]:(~r1_tarski(X34,X35)|k3_xboole_0(X34,X35)=X34), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.68/0.86  cnf(c_0_23, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_14])).
% 0.68/0.86  cnf(c_0_24, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_15])).
% 0.68/0.86  cnf(c_0_25, plain, (r2_hidden(esk4_2(X1,k4_xboole_0(X2,X3)),X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.68/0.86  cnf(c_0_26, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.68/0.86  cnf(c_0_27, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.68/0.86  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.68/0.86  fof(c_0_29, negated_conjecture, ((r2_hidden(esk8_0,esk9_0)&r1_tarski(esk8_0,esk10_0))&~r1_tarski(k1_setfam_1(esk9_0),esk10_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.68/0.86  cnf(c_0_30, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.68/0.86  fof(c_0_31, plain, ![X45, X46, X47, X48, X49, X51, X54, X55, X56, X57]:((((~r2_hidden(X47,X46)|(~r2_hidden(X48,X45)|r2_hidden(X47,X48))|X46!=k1_setfam_1(X45)|X45=k1_xboole_0)&((r2_hidden(esk5_3(X45,X46,X49),X45)|r2_hidden(X49,X46)|X46!=k1_setfam_1(X45)|X45=k1_xboole_0)&(~r2_hidden(X49,esk5_3(X45,X46,X49))|r2_hidden(X49,X46)|X46!=k1_setfam_1(X45)|X45=k1_xboole_0)))&(((r2_hidden(esk7_2(X45,X51),X45)|~r2_hidden(esk6_2(X45,X51),X51)|X51=k1_setfam_1(X45)|X45=k1_xboole_0)&(~r2_hidden(esk6_2(X45,X51),esk7_2(X45,X51))|~r2_hidden(esk6_2(X45,X51),X51)|X51=k1_setfam_1(X45)|X45=k1_xboole_0))&(r2_hidden(esk6_2(X45,X51),X51)|(~r2_hidden(X54,X45)|r2_hidden(esk6_2(X45,X51),X54))|X51=k1_setfam_1(X45)|X45=k1_xboole_0)))&((X56!=k1_setfam_1(X55)|X56=k1_xboole_0|X55!=k1_xboole_0)&(X57!=k1_xboole_0|X57=k1_setfam_1(X55)|X55!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.68/0.86  fof(c_0_32, plain, ![X36, X37]:((k4_xboole_0(X36,X37)!=k1_xboole_0|r1_tarski(X36,X37))&(~r1_tarski(X36,X37)|k4_xboole_0(X36,X37)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 0.68/0.86  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.68/0.86  cnf(c_0_34, plain, (~r2_hidden(esk4_2(X1,k4_xboole_0(X2,X3)),X3)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_23, c_0_17])).
% 0.68/0.86  cnf(c_0_35, plain, (r2_hidden(esk4_2(X1,k4_xboole_0(k3_xboole_0(X2,X3),X4)),X3)|~r2_hidden(X1,k4_xboole_0(k3_xboole_0(X2,X3),X4))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.68/0.86  cnf(c_0_36, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_26])).
% 0.68/0.86  cnf(c_0_37, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.68/0.86  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.68/0.86  cnf(c_0_39, negated_conjecture, (r1_tarski(esk8_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.68/0.86  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.68/0.86  cnf(c_0_41, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)|r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_16, c_0_30])).
% 0.68/0.86  cnf(c_0_42, plain, (r2_hidden(X1,X3)|X4=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X2!=k1_setfam_1(X4)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.68/0.86  cnf(c_0_43, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.68/0.86  cnf(c_0_44, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_24, c_0_33])).
% 0.68/0.86  cnf(c_0_45, plain, (~r2_hidden(X1,k4_xboole_0(k3_xboole_0(X2,X3),X3))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.68/0.86  cnf(c_0_46, plain, (r2_hidden(esk4_2(X1,X2),k4_xboole_0(X2,X3))|r2_hidden(esk4_2(X1,X2),X3)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_17])).
% 0.68/0.86  cnf(c_0_47, negated_conjecture, (r2_hidden(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.68/0.86  cnf(c_0_48, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_37])).
% 0.68/0.86  cnf(c_0_49, negated_conjecture, (r1_tarski(X1,esk10_0)|~r1_tarski(X1,esk8_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.68/0.86  cnf(c_0_50, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.68/0.86  cnf(c_0_51, plain, (X1=k1_xboole_0|r2_hidden(X2,X3)|~r2_hidden(X2,k1_setfam_1(X1))|~r2_hidden(X3,X1)), inference(er,[status(thm)],[c_0_42])).
% 0.68/0.86  cnf(c_0_52, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_23, c_0_43])).
% 0.68/0.86  cnf(c_0_53, plain, (r2_hidden(esk4_2(X1,X2),X3)|~r2_hidden(X1,X2)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_44, c_0_17])).
% 0.68/0.86  cnf(c_0_54, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_45, c_0_33])).
% 0.68/0.86  cnf(c_0_55, negated_conjecture, (r2_hidden(esk4_2(esk8_0,esk9_0),k4_xboole_0(esk9_0,X1))|r2_hidden(esk4_2(esk8_0,esk9_0),X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.68/0.86  cnf(c_0_56, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X3)|~r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_40, c_0_48])).
% 0.68/0.86  cnf(c_0_57, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_44, c_0_30])).
% 0.68/0.86  cnf(c_0_58, negated_conjecture, (r1_tarski(k4_xboole_0(esk8_0,X1),esk10_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.68/0.86  cnf(c_0_59, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(k1_setfam_1(X1),X2),X3)|r1_tarski(k1_setfam_1(X1),X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_51, c_0_30])).
% 0.68/0.86  cnf(c_0_60, plain, (~r2_hidden(esk4_2(X1,k1_xboole_0),X2)|~r2_hidden(X1,k1_xboole_0)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_52, c_0_17])).
% 0.68/0.86  cnf(c_0_61, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X2,X3),X3)), inference(spm,[status(thm)],[c_0_34, c_0_53])).
% 0.68/0.86  cnf(c_0_62, negated_conjecture, (r2_hidden(esk4_2(esk8_0,esk9_0),X1)|~r1_tarski(esk9_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.68/0.86  cnf(c_0_63, plain, (r1_tarski(k4_xboole_0(X1,X2),k3_xboole_0(X3,X1))|~r2_hidden(esk1_2(k4_xboole_0(X1,X2),k3_xboole_0(X3,X1)),X3)), inference(spm,[status(thm)],[c_0_56, c_0_41])).
% 0.68/0.86  cnf(c_0_64, negated_conjecture, (r2_hidden(esk1_2(k4_xboole_0(esk8_0,X1),X2),esk10_0)|r1_tarski(k4_xboole_0(esk8_0,X1),X2)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.68/0.86  cnf(c_0_65, negated_conjecture, (esk9_0=k1_xboole_0|r2_hidden(esk1_2(k1_setfam_1(esk9_0),X1),esk8_0)|r1_tarski(k1_setfam_1(esk9_0),X1)), inference(spm,[status(thm)],[c_0_59, c_0_47])).
% 0.68/0.86  cnf(c_0_66, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_17])).
% 0.68/0.86  cnf(c_0_67, negated_conjecture, (~r1_tarski(esk9_0,k4_xboole_0(X1,X2))|~r1_tarski(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.68/0.86  cnf(c_0_68, negated_conjecture, (r1_tarski(k4_xboole_0(esk8_0,X1),k3_xboole_0(esk10_0,esk8_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.68/0.86  cnf(c_0_69, negated_conjecture, (esk9_0=k1_xboole_0|r1_tarski(k1_setfam_1(esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_40, c_0_65])).
% 0.68/0.86  cnf(c_0_70, negated_conjecture, (~r1_tarski(k1_setfam_1(esk9_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.68/0.86  cnf(c_0_71, plain, (r1_tarski(k1_xboole_0,X1)|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_66, c_0_30])).
% 0.68/0.86  cnf(c_0_72, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_40, c_0_30])).
% 0.68/0.86  cnf(c_0_73, negated_conjecture, (~r1_tarski(esk9_0,k4_xboole_0(esk8_0,k3_xboole_0(esk10_0,esk8_0)))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.68/0.86  cnf(c_0_74, negated_conjecture, (esk9_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_69]), c_0_70])).
% 0.68/0.86  cnf(c_0_75, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.68/0.86  cnf(c_0_76, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74]), c_0_75])]), ['proof']).
% 0.68/0.86  # SZS output end CNFRefutation
% 0.68/0.86  # Proof object total steps             : 77
% 0.68/0.86  # Proof object clause steps            : 56
% 0.68/0.86  # Proof object formula steps           : 21
% 0.68/0.86  # Proof object conjectures             : 18
% 0.68/0.86  # Proof object clause conjectures      : 15
% 0.68/0.86  # Proof object formula conjectures     : 3
% 0.68/0.86  # Proof object initial clauses used    : 16
% 0.68/0.86  # Proof object initial formulas used   : 10
% 0.68/0.86  # Proof object generating inferences   : 33
% 0.68/0.86  # Proof object simplifying inferences  : 10
% 0.68/0.86  # Training examples: 0 positive, 0 negative
% 0.68/0.86  # Parsed axioms                        : 11
% 0.68/0.86  # Removed by relevancy pruning/SinE    : 0
% 0.68/0.86  # Initial clauses                      : 34
% 0.68/0.86  # Removed in clause preprocessing      : 0
% 0.68/0.86  # Initial clauses in saturation        : 34
% 0.68/0.86  # Processed clauses                    : 5662
% 0.68/0.86  # ...of these trivial                  : 29
% 0.68/0.86  # ...subsumed                          : 4490
% 0.68/0.86  # ...remaining for further processing  : 1143
% 0.68/0.86  # Other redundant clauses eliminated   : 13
% 0.68/0.86  # Clauses deleted for lack of memory   : 0
% 0.68/0.86  # Backward-subsumed                    : 62
% 0.68/0.86  # Backward-rewritten                   : 322
% 0.68/0.86  # Generated clauses                    : 41212
% 0.68/0.86  # ...of the previous two non-trivial   : 38589
% 0.68/0.86  # Contextual simplify-reflections      : 12
% 0.68/0.86  # Paramodulations                      : 41109
% 0.68/0.86  # Factorizations                       : 92
% 0.68/0.86  # Equation resolutions                 : 13
% 0.68/0.86  # Propositional unsat checks           : 0
% 0.68/0.86  #    Propositional check models        : 0
% 0.68/0.86  #    Propositional check unsatisfiable : 0
% 0.68/0.86  #    Propositional clauses             : 0
% 0.68/0.86  #    Propositional clauses after purity: 0
% 0.68/0.86  #    Propositional unsat core size     : 0
% 0.68/0.86  #    Propositional preprocessing time  : 0.000
% 0.68/0.86  #    Propositional encoding time       : 0.000
% 0.68/0.86  #    Propositional solver time         : 0.000
% 0.68/0.86  #    Success case prop preproc time    : 0.000
% 0.68/0.86  #    Success case prop encoding time   : 0.000
% 0.68/0.86  #    Success case prop solver time     : 0.000
% 0.68/0.86  # Current number of processed clauses  : 715
% 0.68/0.86  #    Positive orientable unit clauses  : 86
% 0.68/0.86  #    Positive unorientable unit clauses: 0
% 0.68/0.86  #    Negative unit clauses             : 7
% 0.68/0.86  #    Non-unit-clauses                  : 622
% 0.68/0.86  # Current number of unprocessed clauses: 32593
% 0.68/0.86  # ...number of literals in the above   : 129229
% 0.68/0.86  # Current number of archived formulas  : 0
% 0.68/0.86  # Current number of archived clauses   : 417
% 0.68/0.86  # Clause-clause subsumption calls (NU) : 175503
% 0.68/0.86  # Rec. Clause-clause subsumption calls : 89339
% 0.68/0.86  # Non-unit clause-clause subsumptions  : 2755
% 0.68/0.86  # Unit Clause-clause subsumption calls : 12880
% 0.68/0.86  # Rewrite failures with RHS unbound    : 0
% 0.68/0.86  # BW rewrite match attempts            : 244
% 0.68/0.86  # BW rewrite match successes           : 34
% 0.68/0.86  # Condensation attempts                : 0
% 0.68/0.86  # Condensation successes               : 0
% 0.68/0.86  # Termbank termtop insertions          : 619437
% 0.68/0.86  
% 0.68/0.86  # -------------------------------------------------
% 0.68/0.86  # User time                : 0.473 s
% 0.68/0.86  # System time              : 0.031 s
% 0.68/0.86  # Total time               : 0.504 s
% 0.68/0.86  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
