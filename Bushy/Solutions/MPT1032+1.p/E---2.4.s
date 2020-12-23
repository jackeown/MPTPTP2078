%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t141_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:30 EDT 2019

% Result     : Theorem 9.22s
% Output     : CNFRefutation 9.22s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 109 expanded)
%              Number of clauses        :   35 (  53 expanded)
%              Number of leaves         :    4 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  197 ( 693 expanded)
%              Number of equality atoms :   58 ( 228 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k1_funct_2(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( v1_relat_1(X5)
              & v1_funct_1(X5)
              & X4 = X5
              & k1_relat_1(X5) = X1
              & r1_tarski(k2_relat_1(X5),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t141_funct_2.p',d2_funct_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t141_funct_2.p',d3_tarski)).

fof(t141_funct_2,conjecture,(
    ! [X1,X2] : r1_tarski(k1_funct_2(X1,X2),k4_partfun1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t141_funct_2.p',t141_funct_2)).

fof(d5_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_partfun1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( v1_relat_1(X5)
              & v1_funct_1(X5)
              & X4 = X5
              & r1_tarski(k1_relat_1(X5),X1)
              & r1_tarski(k2_relat_1(X5),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t141_funct_2.p',d5_partfun1)).

fof(c_0_4,plain,(
    ! [X10,X11,X12,X13,X15,X16,X17,X18,X19,X21] :
      ( ( v1_relat_1(esk3_4(X10,X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k1_funct_2(X10,X11) )
      & ( v1_funct_1(esk3_4(X10,X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k1_funct_2(X10,X11) )
      & ( X13 = esk3_4(X10,X11,X12,X13)
        | ~ r2_hidden(X13,X12)
        | X12 != k1_funct_2(X10,X11) )
      & ( k1_relat_1(esk3_4(X10,X11,X12,X13)) = X10
        | ~ r2_hidden(X13,X12)
        | X12 != k1_funct_2(X10,X11) )
      & ( r1_tarski(k2_relat_1(esk3_4(X10,X11,X12,X13)),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k1_funct_2(X10,X11) )
      & ( ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | X15 != X16
        | k1_relat_1(X16) != X10
        | ~ r1_tarski(k2_relat_1(X16),X11)
        | r2_hidden(X15,X12)
        | X12 != k1_funct_2(X10,X11) )
      & ( ~ r2_hidden(esk4_3(X17,X18,X19),X19)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21)
        | esk4_3(X17,X18,X19) != X21
        | k1_relat_1(X21) != X17
        | ~ r1_tarski(k2_relat_1(X21),X18)
        | X19 = k1_funct_2(X17,X18) )
      & ( v1_relat_1(esk5_3(X17,X18,X19))
        | r2_hidden(esk4_3(X17,X18,X19),X19)
        | X19 = k1_funct_2(X17,X18) )
      & ( v1_funct_1(esk5_3(X17,X18,X19))
        | r2_hidden(esk4_3(X17,X18,X19),X19)
        | X19 = k1_funct_2(X17,X18) )
      & ( esk4_3(X17,X18,X19) = esk5_3(X17,X18,X19)
        | r2_hidden(esk4_3(X17,X18,X19),X19)
        | X19 = k1_funct_2(X17,X18) )
      & ( k1_relat_1(esk5_3(X17,X18,X19)) = X17
        | r2_hidden(esk4_3(X17,X18,X19),X19)
        | X19 = k1_funct_2(X17,X18) )
      & ( r1_tarski(k2_relat_1(esk5_3(X17,X18,X19)),X18)
        | r2_hidden(esk4_3(X17,X18,X19),X19)
        | X19 = k1_funct_2(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

fof(c_0_5,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( ( ~ r1_tarski(X23,X24)
        | ~ r2_hidden(X25,X23)
        | r2_hidden(X25,X24) )
      & ( r2_hidden(esk6_2(X26,X27),X26)
        | r1_tarski(X26,X27) )
      & ( ~ r2_hidden(esk6_2(X26,X27),X27)
        | r1_tarski(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_6,plain,
    ( k1_relat_1(esk3_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( X1 = esk3_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( v1_funct_1(esk3_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( v1_relat_1(esk3_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k1_funct_2(X1,X2),k4_partfun1(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t141_funct_2])).

cnf(c_0_11,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r2_hidden(esk6_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( k1_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3)) = X1
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( esk3_4(X1,X2,k1_funct_2(X1,X2),X3) = X3
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( v1_funct_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( v1_relat_1(esk3_4(X1,X2,k1_funct_2(X1,X2),X3))
    | ~ r2_hidden(X3,k1_funct_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_9])).

fof(c_0_17,negated_conjecture,(
    ~ r1_tarski(k1_funct_2(esk1_0,esk2_0),k4_partfun1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_18,plain,
    ( r2_hidden(esk6_2(X1,X2),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_19,plain,(
    ! [X29,X30,X31,X32,X34,X35,X36,X37,X38,X40] :
      ( ( v1_relat_1(esk7_4(X29,X30,X31,X32))
        | ~ r2_hidden(X32,X31)
        | X31 != k4_partfun1(X29,X30) )
      & ( v1_funct_1(esk7_4(X29,X30,X31,X32))
        | ~ r2_hidden(X32,X31)
        | X31 != k4_partfun1(X29,X30) )
      & ( X32 = esk7_4(X29,X30,X31,X32)
        | ~ r2_hidden(X32,X31)
        | X31 != k4_partfun1(X29,X30) )
      & ( r1_tarski(k1_relat_1(esk7_4(X29,X30,X31,X32)),X29)
        | ~ r2_hidden(X32,X31)
        | X31 != k4_partfun1(X29,X30) )
      & ( r1_tarski(k2_relat_1(esk7_4(X29,X30,X31,X32)),X30)
        | ~ r2_hidden(X32,X31)
        | X31 != k4_partfun1(X29,X30) )
      & ( ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35)
        | X34 != X35
        | ~ r1_tarski(k1_relat_1(X35),X29)
        | ~ r1_tarski(k2_relat_1(X35),X30)
        | r2_hidden(X34,X31)
        | X31 != k4_partfun1(X29,X30) )
      & ( ~ r2_hidden(esk8_3(X36,X37,X38),X38)
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40)
        | esk8_3(X36,X37,X38) != X40
        | ~ r1_tarski(k1_relat_1(X40),X36)
        | ~ r1_tarski(k2_relat_1(X40),X37)
        | X38 = k4_partfun1(X36,X37) )
      & ( v1_relat_1(esk9_3(X36,X37,X38))
        | r2_hidden(esk8_3(X36,X37,X38),X38)
        | X38 = k4_partfun1(X36,X37) )
      & ( v1_funct_1(esk9_3(X36,X37,X38))
        | r2_hidden(esk8_3(X36,X37,X38),X38)
        | X38 = k4_partfun1(X36,X37) )
      & ( esk8_3(X36,X37,X38) = esk9_3(X36,X37,X38)
        | r2_hidden(esk8_3(X36,X37,X38),X38)
        | X38 = k4_partfun1(X36,X37) )
      & ( r1_tarski(k1_relat_1(esk9_3(X36,X37,X38)),X36)
        | r2_hidden(esk8_3(X36,X37,X38),X38)
        | X38 = k4_partfun1(X36,X37) )
      & ( r1_tarski(k2_relat_1(esk9_3(X36,X37,X38)),X37)
        | r2_hidden(esk8_3(X36,X37,X38),X38)
        | X38 = k4_partfun1(X36,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_partfun1])])])])])])).

cnf(c_0_20,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_22,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_tarski(k1_funct_2(esk1_0,esk2_0),k4_partfun1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(esk6_2(X1,X2),X3)
    | r2_hidden(esk6_2(X1,X3),X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_12])).

cnf(c_0_25,plain,
    ( r2_hidden(X2,X5)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | X2 != X1
    | ~ r1_tarski(k1_relat_1(X1),X3)
    | ~ r1_tarski(k2_relat_1(X1),X4)
    | X5 != k4_partfun1(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k1_relat_1(esk6_2(k1_funct_2(X1,X2),X3)) = X1
    | r1_tarski(k1_funct_2(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_12])).

cnf(c_0_27,plain,
    ( v1_funct_1(esk6_2(k1_funct_2(X1,X2),X3))
    | r1_tarski(k1_funct_2(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_12])).

cnf(c_0_28,plain,
    ( v1_relat_1(esk6_2(k1_funct_2(X1,X2),X3))
    | r1_tarski(k1_funct_2(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_12])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_relat_1(esk3_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk6_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk6_2(k1_funct_2(esk1_0,esk2_0),X1),k1_funct_2(esk1_0,esk2_0))
    | r2_hidden(esk6_2(k1_funct_2(esk1_0,esk2_0),k4_partfun1(esk1_0,esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | X2 != k4_partfun1(X3,X4)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X3)
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(esk6_2(k1_funct_2(esk1_0,esk2_0),k4_partfun1(esk1_0,esk2_0))) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk6_2(k1_funct_2(esk1_0,esk2_0),k4_partfun1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk6_2(k1_funct_2(esk1_0,esk2_0),k4_partfun1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk6_2(k1_funct_2(esk1_0,esk2_0),k4_partfun1(esk1_0,esk2_0)),k1_funct_2(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk6_2(k1_funct_2(esk1_0,esk2_0),k4_partfun1(esk1_0,esk2_0)),X1)
    | X1 != k4_partfun1(X2,X3)
    | ~ r1_tarski(k2_relat_1(esk6_2(k1_funct_2(esk1_0,esk2_0),k4_partfun1(esk1_0,esk2_0))),X3)
    | ~ r1_tarski(esk1_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_2(k1_funct_2(esk1_0,esk2_0),k4_partfun1(esk1_0,esk2_0))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk6_2(k1_funct_2(esk1_0,esk2_0),k4_partfun1(esk1_0,esk2_0)),X1)
    | X1 != k4_partfun1(X2,esk2_0)
    | ~ r1_tarski(esk1_0,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk6_2(k1_funct_2(esk1_0,esk2_0),k4_partfun1(esk1_0,esk2_0)),k4_partfun1(X1,esk2_0))
    | ~ r1_tarski(esk1_0,X1) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_12])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_41]),c_0_42])]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
