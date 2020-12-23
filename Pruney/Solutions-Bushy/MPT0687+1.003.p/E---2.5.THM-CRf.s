%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0687+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:02 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 377 expanded)
%              Number of clauses        :   43 ( 203 expanded)
%              Number of leaves         :    7 (  98 expanded)
%              Depth                    :   15
%              Number of atoms          :  183 (1212 expanded)
%              Number of equality atoms :   58 ( 504 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(t142_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k2_relat_1(X2))
      <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(c_0_7,plain,(
    ! [X36] :
      ( ~ v1_xboole_0(X36)
      | X36 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_8,plain,(
    ! [X37,X38] :
      ( ~ r2_hidden(X37,X38)
      | ~ v1_xboole_0(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_9,plain,(
    ! [X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X20,X19)
        | X20 = X18
        | X19 != k1_tarski(X18) )
      & ( X21 != X18
        | r2_hidden(X21,X19)
        | X19 != k1_tarski(X18) )
      & ( ~ r2_hidden(esk4_2(X22,X23),X23)
        | esk4_2(X22,X23) != X22
        | X23 = k1_tarski(X22) )
      & ( r2_hidden(esk4_2(X22,X23),X23)
        | esk4_2(X22,X23) = X22
        | X23 = k1_tarski(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_10,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | esk4_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( esk4_2(X1,X2) = X1
    | X2 = k1_tarski(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_11,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_15])])).

cnf(c_0_19,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk4_2(X1,X2),X2)
    | esk4_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( esk4_2(X1,k1_xboole_0) = X1
    | k1_tarski(X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,plain,(
    ! [X25,X26,X27,X29,X30,X31,X32,X34] :
      ( ( ~ r2_hidden(X27,X26)
        | r2_hidden(k4_tarski(esk5_3(X25,X26,X27),X27),X25)
        | X26 != k2_relat_1(X25) )
      & ( ~ r2_hidden(k4_tarski(X30,X29),X25)
        | r2_hidden(X29,X26)
        | X26 != k2_relat_1(X25) )
      & ( ~ r2_hidden(esk6_2(X31,X32),X32)
        | ~ r2_hidden(k4_tarski(X34,esk6_2(X31,X32)),X31)
        | X32 = k2_relat_1(X31) )
      & ( r2_hidden(esk6_2(X31,X32),X32)
        | r2_hidden(k4_tarski(esk7_2(X31,X32),esk6_2(X31,X32)),X31)
        | X32 = k2_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_22,plain,(
    ! [X6,X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( r2_hidden(k4_tarski(X9,esk1_4(X6,X7,X8,X9)),X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k10_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k10_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(X11,X12),X6)
        | ~ r2_hidden(X12,X7)
        | r2_hidden(X11,X8)
        | X8 != k10_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(esk2_3(X6,X13,X14),X14)
        | ~ r2_hidden(k4_tarski(esk2_3(X6,X13,X14),X16),X6)
        | ~ r2_hidden(X16,X13)
        | X14 = k10_relat_1(X6,X13)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(esk2_3(X6,X13,X14),esk3_3(X6,X13,X14)),X6)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k10_relat_1(X6,X13)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk3_3(X6,X13,X14),X13)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k10_relat_1(X6,X13)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_23,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_18])).

cnf(c_0_24,plain,
    ( k1_tarski(X1) = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,X4,X1)),X2)
    | ~ r2_hidden(X1,X4)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_17])])).

cnf(c_0_30,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,k10_relat_1(X2,X3),X1)),X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_4(X1,X2,k10_relat_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( X1 = k2_relat_1(k1_xboole_0)
    | r2_hidden(esk6_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_4(X1,X2,k10_relat_1(X1,X2),X3),k2_relat_1(X1))
    | ~ r2_hidden(X3,k10_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( esk1_4(X1,k1_tarski(X2),k10_relat_1(X1,k1_tarski(X2)),X3) = X2
    | ~ r2_hidden(X3,k10_relat_1(X1,k1_tarski(X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_35])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
        <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t142_funct_1])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(X3,k10_relat_1(X2,k1_tarski(X1)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk6_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_35,c_0_38])).

fof(c_0_44,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & ( ~ r2_hidden(esk8_0,k2_relat_1(esk9_0))
      | k10_relat_1(esk9_0,k1_tarski(esk8_0)) = k1_xboole_0 )
    & ( r2_hidden(esk8_0,k2_relat_1(esk9_0))
      | k10_relat_1(esk9_0,k1_tarski(esk8_0)) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0
    | r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,plain,
    ( r2_hidden(esk5_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( k10_relat_1(esk9_0,k1_tarski(esk8_0)) = k1_xboole_0
    | ~ r2_hidden(esk8_0,k2_relat_1(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk8_0,k2_relat_1(esk9_0))
    | k10_relat_1(esk9_0,k1_tarski(esk8_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( k10_relat_1(esk9_0,k1_tarski(X1)) = k1_xboole_0
    | r2_hidden(X1,k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k2_relat_1(esk9_0))
    | ~ r2_hidden(X1,k2_relat_1(esk9_0))
    | ~ r2_hidden(X1,k1_tarski(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_48])]),c_0_29])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk8_0,k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk9_0))
    | ~ r2_hidden(X1,k1_tarski(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_54]),c_0_18])]),
    [proof]).

%------------------------------------------------------------------------------
