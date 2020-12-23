%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t148_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:51 EDT 2019

% Result     : Theorem 264.50s
% Output     : CNFRefutation 264.50s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 153 expanded)
%              Number of clauses        :   30 (  70 expanded)
%              Number of leaves         :    5 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  187 ( 779 expanded)
%              Number of equality atoms :   43 ( 190 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t148_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t148_relat_1.p',t148_relat_1)).

fof(d11_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( v1_relat_1(X3)
         => ( X3 = k7_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X4,X2)
                  & r2_hidden(k4_tarski(X4,X5),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t148_relat_1.p',d11_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t148_relat_1.p',dt_k7_relat_1)).

fof(d13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t148_relat_1.p',d13_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t148_relat_1.p',d5_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t148_relat_1])).

fof(c_0_6,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X13,X11)
        | ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X12 != k7_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(X13,X14),X10)
        | ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X12 != k7_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(k4_tarski(X15,X16),X10)
        | r2_hidden(k4_tarski(X15,X16),X12)
        | X12 != k7_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(k4_tarski(esk3_3(X10,X11,X12),esk4_3(X10,X11,X12)),X12)
        | ~ r2_hidden(esk3_3(X10,X11,X12),X11)
        | ~ r2_hidden(k4_tarski(esk3_3(X10,X11,X12),esk4_3(X10,X11,X12)),X10)
        | X12 = k7_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk3_3(X10,X11,X12),X11)
        | r2_hidden(k4_tarski(esk3_3(X10,X11,X12),esk4_3(X10,X11,X12)),X12)
        | X12 = k7_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(esk3_3(X10,X11,X12),esk4_3(X10,X11,X12)),X10)
        | r2_hidden(k4_tarski(esk3_3(X10,X11,X12),esk4_3(X10,X11,X12)),X12)
        | X12 = k7_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).

fof(c_0_7,plain,(
    ! [X42,X43] :
      ( ~ v1_relat_1(X42)
      | v1_relat_1(k7_relat_1(X42,X43)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_8,plain,(
    ! [X19,X20,X21,X22,X24,X25,X26,X27,X29] :
      ( ( r2_hidden(k4_tarski(esk5_4(X19,X20,X21,X22),X22),X19)
        | ~ r2_hidden(X22,X21)
        | X21 != k9_relat_1(X19,X20)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk5_4(X19,X20,X21,X22),X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k9_relat_1(X19,X20)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(X25,X24),X19)
        | ~ r2_hidden(X25,X20)
        | r2_hidden(X24,X21)
        | X21 != k9_relat_1(X19,X20)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(esk6_3(X19,X26,X27),X27)
        | ~ r2_hidden(k4_tarski(X29,esk6_3(X19,X26,X27)),X19)
        | ~ r2_hidden(X29,X26)
        | X27 = k9_relat_1(X19,X26)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk7_3(X19,X26,X27),esk6_3(X19,X26,X27)),X19)
        | r2_hidden(esk6_3(X19,X26,X27),X27)
        | X27 = k9_relat_1(X19,X26)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk7_3(X19,X26,X27),X26)
        | r2_hidden(esk6_3(X19,X26,X27),X27)
        | X27 = k9_relat_1(X19,X26)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & k2_relat_1(k7_relat_1(esk2_0,esk1_0)) != k9_relat_1(esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_10,plain,(
    ! [X31,X32,X33,X35,X36,X37,X38,X40] :
      ( ( ~ r2_hidden(X33,X32)
        | r2_hidden(k4_tarski(esk8_3(X31,X32,X33),X33),X31)
        | X32 != k2_relat_1(X31) )
      & ( ~ r2_hidden(k4_tarski(X36,X35),X31)
        | r2_hidden(X35,X32)
        | X32 != k2_relat_1(X31) )
      & ( ~ r2_hidden(esk9_2(X37,X38),X38)
        | ~ r2_hidden(k4_tarski(X40,esk9_2(X37,X38)),X37)
        | X38 = k2_relat_1(X37) )
      & ( r2_hidden(esk9_2(X37,X38),X38)
        | r2_hidden(k4_tarski(esk10_2(X37,X38),esk9_2(X37,X38)),X37)
        | X38 = k2_relat_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(X1,X3),X5)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X5 != k7_relat_1(X4,X2)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(esk7_3(X1,X2,X3),esk6_3(X1,X2,X3)),X1)
    | r2_hidden(esk6_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( X1 = k9_relat_1(esk2_0,X2)
    | r2_hidden(k4_tarski(esk7_3(esk2_0,X2,X1),esk6_3(esk2_0,X2,X1)),esk2_0)
    | r2_hidden(esk6_3(esk2_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( X1 = k9_relat_1(esk2_0,X2)
    | r2_hidden(k4_tarski(esk7_3(esk2_0,X2,X1),esk6_3(esk2_0,X2,X1)),k7_relat_1(esk2_0,X3))
    | r2_hidden(esk6_3(esk2_0,X2,X1),X1)
    | ~ r2_hidden(esk7_3(esk2_0,X2,X1),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_14])])).

cnf(c_0_20,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X2)
    | r2_hidden(esk6_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | X4 != k7_relat_1(X3,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k7_relat_1(X5,X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( X1 = k9_relat_1(esk2_0,X2)
    | r2_hidden(esk6_3(esk2_0,X2,X1),k2_relat_1(k7_relat_1(esk2_0,X3)))
    | r2_hidden(esk6_3(esk2_0,X2,X1),X1)
    | ~ r2_hidden(esk7_3(esk2_0,X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( X1 = k9_relat_1(esk2_0,X2)
    | r2_hidden(esk6_3(esk2_0,X2,X1),X1)
    | r2_hidden(esk7_3(esk2_0,X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_14])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_12])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(esk8_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k7_relat_1(X4,X2))
    | ~ v1_relat_1(X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k9_relat_1(esk2_0,X2)
    | r2_hidden(esk6_3(esk2_0,X2,X1),k2_relat_1(k7_relat_1(esk2_0,X2)))
    | r2_hidden(esk6_3(esk2_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(esk8_3(k7_relat_1(X1,X2),X3,X4),X4),X1)
    | X3 != k2_relat_1(k7_relat_1(X1,X2))
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(esk8_3(k7_relat_1(X1,X2),X3,X4),X2)
    | X3 != k2_relat_1(k7_relat_1(X1,X2))
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_31,plain,
    ( X3 = k9_relat_1(X1,X2)
    | ~ r2_hidden(esk6_3(X1,X2,X3),X3)
    | ~ r2_hidden(k4_tarski(X4,esk6_3(X1,X2,X3)),X1)
    | ~ r2_hidden(X4,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,X1)) = k9_relat_1(esk2_0,X1)
    | r2_hidden(esk6_3(esk2_0,X1,k2_relat_1(k7_relat_1(esk2_0,X1))),k2_relat_1(k7_relat_1(esk2_0,X1))) ),
    inference(ef,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(esk8_3(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2)),X3),X3),X1)
    | ~ r2_hidden(X3,k2_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(esk8_3(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2)),X3),X2)
    | ~ r2_hidden(X3,k2_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,X1)) = k9_relat_1(esk2_0,X1)
    | ~ r2_hidden(k4_tarski(X2,esk6_3(esk2_0,X1,k2_relat_1(k7_relat_1(esk2_0,X1)))),esk2_0)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_14])])).

cnf(c_0_36,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,X1)) = k9_relat_1(esk2_0,X1)
    | r2_hidden(k4_tarski(esk8_3(k7_relat_1(esk2_0,X1),k2_relat_1(k7_relat_1(esk2_0,X1)),esk6_3(esk2_0,X1,k2_relat_1(k7_relat_1(esk2_0,X1)))),esk6_3(esk2_0,X1,k2_relat_1(k7_relat_1(esk2_0,X1)))),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_32]),c_0_14])])).

cnf(c_0_37,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,X1)) = k9_relat_1(esk2_0,X1)
    | r2_hidden(esk8_3(k7_relat_1(esk2_0,X1),k2_relat_1(k7_relat_1(esk2_0,X1)),esk6_3(esk2_0,X1,k2_relat_1(k7_relat_1(esk2_0,X1)))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_32]),c_0_14])])).

cnf(c_0_38,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,esk1_0)) != k9_relat_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,X1)) = k9_relat_1(esk2_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
