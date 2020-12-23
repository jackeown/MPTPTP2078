%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t182_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:55 EDT 2019

% Result     : Theorem 267.97s
% Output     : CNFRefutation 267.97s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 260 expanded)
%              Number of clauses        :   42 ( 117 expanded)
%              Number of leaves         :    5 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  249 (1313 expanded)
%              Number of equality atoms :   48 ( 300 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t182_relat_1.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t182_relat_1.p',dt_k5_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t182_relat_1.p',d4_relat_1)).

fof(t182_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t182_relat_1.p',t182_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/relat_1__t182_relat_1.p',d14_relat_1)).

fof(c_0_5,plain,(
    ! [X34,X35,X36,X37,X38,X40,X41,X42,X45] :
      ( ( r2_hidden(k4_tarski(X37,esk9_5(X34,X35,X36,X37,X38)),X34)
        | ~ r2_hidden(k4_tarski(X37,X38),X36)
        | X36 != k5_relat_1(X34,X35)
        | ~ v1_relat_1(X36)
        | ~ v1_relat_1(X35)
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(k4_tarski(esk9_5(X34,X35,X36,X37,X38),X38),X35)
        | ~ r2_hidden(k4_tarski(X37,X38),X36)
        | X36 != k5_relat_1(X34,X35)
        | ~ v1_relat_1(X36)
        | ~ v1_relat_1(X35)
        | ~ v1_relat_1(X34) )
      & ( ~ r2_hidden(k4_tarski(X40,X42),X34)
        | ~ r2_hidden(k4_tarski(X42,X41),X35)
        | r2_hidden(k4_tarski(X40,X41),X36)
        | X36 != k5_relat_1(X34,X35)
        | ~ v1_relat_1(X36)
        | ~ v1_relat_1(X35)
        | ~ v1_relat_1(X34) )
      & ( ~ r2_hidden(k4_tarski(esk10_3(X34,X35,X36),esk11_3(X34,X35,X36)),X36)
        | ~ r2_hidden(k4_tarski(esk10_3(X34,X35,X36),X45),X34)
        | ~ r2_hidden(k4_tarski(X45,esk11_3(X34,X35,X36)),X35)
        | X36 = k5_relat_1(X34,X35)
        | ~ v1_relat_1(X36)
        | ~ v1_relat_1(X35)
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(k4_tarski(esk10_3(X34,X35,X36),esk12_3(X34,X35,X36)),X34)
        | r2_hidden(k4_tarski(esk10_3(X34,X35,X36),esk11_3(X34,X35,X36)),X36)
        | X36 = k5_relat_1(X34,X35)
        | ~ v1_relat_1(X36)
        | ~ v1_relat_1(X35)
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(k4_tarski(esk12_3(X34,X35,X36),esk11_3(X34,X35,X36)),X35)
        | r2_hidden(k4_tarski(esk10_3(X34,X35,X36),esk11_3(X34,X35,X36)),X36)
        | X36 = k5_relat_1(X34,X35)
        | ~ v1_relat_1(X36)
        | ~ v1_relat_1(X35)
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_6,plain,(
    ! [X47,X48] :
      ( ~ v1_relat_1(X47)
      | ~ v1_relat_1(X48)
      | v1_relat_1(k5_relat_1(X47,X48)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(X1,esk9_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X23,X24,X25,X27,X28,X29,X30,X32] :
      ( ( ~ r2_hidden(X25,X24)
        | r2_hidden(k4_tarski(X25,esk6_3(X23,X24,X25)),X23)
        | X24 != k1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(X27,X28),X23)
        | r2_hidden(X27,X24)
        | X24 != k1_relat_1(X23) )
      & ( ~ r2_hidden(esk7_2(X29,X30),X30)
        | ~ r2_hidden(k4_tarski(esk7_2(X29,X30),X32),X29)
        | X30 = k1_relat_1(X29) )
      & ( r2_hidden(esk7_2(X29,X30),X30)
        | r2_hidden(k4_tarski(esk7_2(X29,X30),esk8_2(X29,X30)),X29)
        | X30 = k1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t182_relat_1])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(esk9_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,esk9_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_7]),c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk7_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk7_2(X1,X2),esk8_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & k1_relat_1(k5_relat_1(esk1_0,esk2_0)) != k10_relat_1(esk1_0,k1_relat_1(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(esk9_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_8])).

fof(c_0_16,plain,(
    ! [X11,X12,X13,X14,X16,X17,X18,X19,X21] :
      ( ( r2_hidden(k4_tarski(X14,esk3_4(X11,X12,X13,X14)),X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k10_relat_1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk3_4(X11,X12,X13,X14),X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k10_relat_1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(X16,X17),X11)
        | ~ r2_hidden(X17,X12)
        | r2_hidden(X16,X13)
        | X13 != k10_relat_1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(esk4_3(X11,X18,X19),X19)
        | ~ r2_hidden(k4_tarski(esk4_3(X11,X18,X19),X21),X11)
        | ~ r2_hidden(X21,X18)
        | X19 = k10_relat_1(X11,X18)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk4_3(X11,X18,X19),esk5_3(X11,X18,X19)),X11)
        | r2_hidden(esk4_3(X11,X18,X19),X19)
        | X19 = k10_relat_1(X11,X18)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk5_3(X11,X18,X19),X18)
        | r2_hidden(esk4_3(X11,X18,X19),X19)
        | X19 = k10_relat_1(X11,X18)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_17,plain,
    ( X1 = k1_relat_1(k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(esk7_2(k5_relat_1(X2,X3),X1),esk9_5(X2,X3,k5_relat_1(X2,X3),esk7_2(k5_relat_1(X2,X3),X1),esk8_2(k5_relat_1(X2,X3),X1))),X2)
    | r2_hidden(esk7_2(k5_relat_1(X2,X3),X1),X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( X1 = k1_relat_1(k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(esk9_5(X2,X3,k5_relat_1(X2,X3),esk7_2(k5_relat_1(X2,X3),X1),esk8_2(k5_relat_1(X2,X3),X1)),esk8_2(k5_relat_1(X2,X3),X1)),X3)
    | r2_hidden(esk7_2(k5_relat_1(X2,X3),X1),X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( X1 = k1_relat_1(k5_relat_1(esk1_0,X2))
    | r2_hidden(k4_tarski(esk7_2(k5_relat_1(esk1_0,X2),X1),esk9_5(esk1_0,X2,k5_relat_1(esk1_0,X2),esk7_2(k5_relat_1(esk1_0,X2),X1),esk8_2(k5_relat_1(esk1_0,X2),X1))),esk1_0)
    | r2_hidden(esk7_2(k5_relat_1(esk1_0,X2),X1),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( X1 = k1_relat_1(k5_relat_1(esk1_0,X2))
    | r2_hidden(k4_tarski(esk9_5(esk1_0,X2,k5_relat_1(esk1_0,X2),esk7_2(k5_relat_1(esk1_0,X2),X1),esk8_2(k5_relat_1(esk1_0,X2),X1)),esk8_2(k5_relat_1(esk1_0,X2),X1)),X2)
    | r2_hidden(esk7_2(k5_relat_1(esk1_0,X2),X1),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( X1 = k1_relat_1(k5_relat_1(esk1_0,esk2_0))
    | r2_hidden(k4_tarski(esk7_2(k5_relat_1(esk1_0,esk2_0),X1),esk9_5(esk1_0,esk2_0,k5_relat_1(esk1_0,esk2_0),esk7_2(k5_relat_1(esk1_0,esk2_0),X1),esk8_2(k5_relat_1(esk1_0,esk2_0),X1))),esk1_0)
    | r2_hidden(esk7_2(k5_relat_1(esk1_0,esk2_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k1_relat_1(k5_relat_1(esk1_0,esk2_0))
    | r2_hidden(k4_tarski(esk9_5(esk1_0,esk2_0,k5_relat_1(esk1_0,esk2_0),esk7_2(k5_relat_1(esk1_0,esk2_0),X1),esk8_2(k5_relat_1(esk1_0,esk2_0),X1)),esk8_2(k5_relat_1(esk1_0,esk2_0),X1)),esk2_0)
    | r2_hidden(esk7_2(k5_relat_1(esk1_0,esk2_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( X1 = k1_relat_1(k5_relat_1(esk1_0,esk2_0))
    | r2_hidden(esk7_2(k5_relat_1(esk1_0,esk2_0),X1),k10_relat_1(esk1_0,X2))
    | r2_hidden(esk7_2(k5_relat_1(esk1_0,esk2_0),X1),X1)
    | ~ r2_hidden(esk9_5(esk1_0,esk2_0,k5_relat_1(esk1_0,esk2_0),esk7_2(k5_relat_1(esk1_0,esk2_0),X1),esk8_2(k5_relat_1(esk1_0,esk2_0),X1)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_18])])).

cnf(c_0_30,negated_conjecture,
    ( X1 = k1_relat_1(k5_relat_1(esk1_0,esk2_0))
    | r2_hidden(esk9_5(esk1_0,esk2_0,k5_relat_1(esk1_0,esk2_0),esk7_2(k5_relat_1(esk1_0,esk2_0),X1),esk8_2(k5_relat_1(esk1_0,esk2_0),X1)),k1_relat_1(esk2_0))
    | r2_hidden(esk7_2(k5_relat_1(esk1_0,esk2_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_32,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k1_relat_1(k5_relat_1(esk1_0,esk2_0))
    | r2_hidden(esk7_2(k5_relat_1(esk1_0,esk2_0),X1),k10_relat_1(esk1_0,k1_relat_1(esk2_0)))
    | r2_hidden(esk7_2(k5_relat_1(esk1_0,esk2_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk1_0,esk2_0)) != k10_relat_1(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X5,X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_31]),c_0_8])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X1,esk6_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,plain,
    ( r2_hidden(esk3_4(X1,X2,k10_relat_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( X1 = k1_relat_1(X2)
    | r2_hidden(esk7_2(X2,X1),k1_relat_1(X2))
    | r2_hidden(esk7_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_13])).

cnf(c_0_39,plain,
    ( X2 = k1_relat_1(X1)
    | ~ r2_hidden(esk7_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(esk7_2(X1,X2),X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk7_2(k5_relat_1(esk1_0,esk2_0),k10_relat_1(esk1_0,k1_relat_1(esk2_0))),k10_relat_1(esk1_0,k1_relat_1(esk2_0))) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_33]),c_0_34])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(X1,esk6_3(X2,X3,X4)),k5_relat_1(X5,X2))
    | X3 != k1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X5)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X5) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( k10_relat_1(X1,X2) = k1_relat_1(X3)
    | r2_hidden(esk3_4(X1,X2,k10_relat_1(X1,X2),esk7_2(X3,k10_relat_1(X1,X2))),X2)
    | r2_hidden(esk7_2(X3,k10_relat_1(X1,X2)),k1_relat_1(X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( r2_hidden(k4_tarski(X1,esk3_4(X2,X3,X4,X1)),X2)
    | ~ r2_hidden(X1,X4)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk7_2(k5_relat_1(esk1_0,esk2_0),k10_relat_1(esk1_0,k1_relat_1(esk2_0))),X1),k5_relat_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_34])).

cnf(c_0_45,plain,
    ( r2_hidden(k4_tarski(X1,esk6_3(X2,k1_relat_1(X2),X3)),k5_relat_1(X4,X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k10_relat_1(esk1_0,X1) = k1_relat_1(X2)
    | r2_hidden(esk3_4(esk1_0,X1,k10_relat_1(esk1_0,X1),esk7_2(X2,k10_relat_1(esk1_0,X1))),X1)
    | r2_hidden(esk7_2(X2,k10_relat_1(esk1_0,X1)),k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_18])).

cnf(c_0_47,plain,
    ( r2_hidden(k4_tarski(X1,esk3_4(X2,X3,k10_relat_1(X2,X3),X1)),X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( X1 != k1_relat_1(k5_relat_1(esk1_0,esk2_0))
    | ~ r2_hidden(esk7_2(k5_relat_1(esk1_0,esk2_0),k10_relat_1(esk1_0,k1_relat_1(esk2_0))),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( k10_relat_1(esk1_0,k1_relat_1(X1)) = k1_relat_1(X2)
    | r2_hidden(k4_tarski(X3,esk6_3(X1,k1_relat_1(X1),esk3_4(esk1_0,k1_relat_1(X1),k10_relat_1(esk1_0,k1_relat_1(X1)),esk7_2(X2,k10_relat_1(esk1_0,k1_relat_1(X1)))))),k5_relat_1(X4,X1))
    | r2_hidden(esk7_2(X2,k10_relat_1(esk1_0,k1_relat_1(X1))),k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,esk3_4(esk1_0,k1_relat_1(X1),k10_relat_1(esk1_0,k1_relat_1(X1)),esk7_2(X2,k10_relat_1(esk1_0,k1_relat_1(X1))))),X4)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X4) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_2(k5_relat_1(esk1_0,esk2_0),k10_relat_1(esk1_0,k1_relat_1(esk2_0))),esk3_4(esk1_0,k1_relat_1(esk2_0),k10_relat_1(esk1_0,k1_relat_1(esk2_0)),esk7_2(k5_relat_1(esk1_0,esk2_0),k10_relat_1(esk1_0,k1_relat_1(esk2_0))))),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_40]),c_0_18])])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(esk7_2(k5_relat_1(esk1_0,esk2_0),k10_relat_1(esk1_0,k1_relat_1(esk2_0))),k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_22]),c_0_18])]),c_0_34]),c_0_44]),c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
