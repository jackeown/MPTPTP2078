%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t86_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:05 EDT 2019

% Result     : Theorem 7.31s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 123 expanded)
%              Number of clauses        :   29 (  57 expanded)
%              Number of leaves         :    4 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  175 ( 673 expanded)
%              Number of equality atoms :   34 ( 115 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/relat_1__t86_relat_1.p',d11_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t86_relat_1.p',d4_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t86_relat_1.p',dt_k7_relat_1)).

fof(t86_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t86_relat_1.p',t86_relat_1)).

fof(c_0_4,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17] :
      ( ( r2_hidden(X14,X12)
        | ~ r2_hidden(k4_tarski(X14,X15),X13)
        | X13 != k7_relat_1(X11,X12)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(X14,X15),X11)
        | ~ r2_hidden(k4_tarski(X14,X15),X13)
        | X13 != k7_relat_1(X11,X12)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(X16,X12)
        | ~ r2_hidden(k4_tarski(X16,X17),X11)
        | r2_hidden(k4_tarski(X16,X17),X13)
        | X13 != k7_relat_1(X11,X12)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk4_3(X11,X12,X13),esk5_3(X11,X12,X13)),X13)
        | ~ r2_hidden(esk4_3(X11,X12,X13),X12)
        | ~ r2_hidden(k4_tarski(esk4_3(X11,X12,X13),esk5_3(X11,X12,X13)),X11)
        | X13 = k7_relat_1(X11,X12)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk4_3(X11,X12,X13),X12)
        | r2_hidden(k4_tarski(esk4_3(X11,X12,X13),esk5_3(X11,X12,X13)),X13)
        | X13 = k7_relat_1(X11,X12)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk4_3(X11,X12,X13),esk5_3(X11,X12,X13)),X11)
        | r2_hidden(k4_tarski(esk4_3(X11,X12,X13),esk5_3(X11,X12,X13)),X13)
        | X13 = k7_relat_1(X11,X12)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).

fof(c_0_5,plain,(
    ! [X20,X21,X22,X24,X25,X26,X27,X29] :
      ( ( ~ r2_hidden(X22,X21)
        | r2_hidden(k4_tarski(X22,esk6_3(X20,X21,X22)),X20)
        | X21 != k1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X24,X25),X20)
        | r2_hidden(X24,X21)
        | X21 != k1_relat_1(X20) )
      & ( ~ r2_hidden(esk7_2(X26,X27),X27)
        | ~ r2_hidden(k4_tarski(esk7_2(X26,X27),X29),X26)
        | X27 = k1_relat_1(X26) )
      & ( r2_hidden(esk7_2(X26,X27),X27)
        | r2_hidden(k4_tarski(esk7_2(X26,X27),esk8_2(X26,X27)),X26)
        | X27 = k1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | X4 != k7_relat_1(X3,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(X1,esk6_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X31)
      | v1_relat_1(k7_relat_1(X31,X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(X1,esk6_3(X2,X3,X1)),X4)
    | X2 != k7_relat_1(X4,X5)
    | X3 != k1_relat_1(X2)
    | ~ r2_hidden(X1,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k7_relat_1(X5,X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,X3),X5)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X5 != k7_relat_1(X4,X2)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,esk6_3(k7_relat_1(X2,X3),X4,X1)),X2)
    | X4 != k1_relat_1(k7_relat_1(X2,X3))
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
        <=> ( r2_hidden(X1,X2)
            & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t86_relat_1])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | X3 != k7_relat_1(X4,X2)
    | X5 != k1_relat_1(X3)
    | ~ r2_hidden(X1,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_7])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,esk6_3(X2,X3,X1)),X4)
    | X4 != k7_relat_1(X2,X5)
    | X3 != k1_relat_1(X2)
    | ~ r2_hidden(X1,X5)
    | ~ r2_hidden(X1,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_7])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_relat_1(k7_relat_1(X4,X5))
    | X2 != k1_relat_1(X4)
    | ~ r2_hidden(X1,X3)
    | ~ v1_relat_1(X4) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ( ~ r2_hidden(esk1_0,k1_relat_1(k7_relat_1(esk3_0,esk2_0)))
      | ~ r2_hidden(esk1_0,esk2_0)
      | ~ r2_hidden(esk1_0,k1_relat_1(esk3_0)) )
    & ( r2_hidden(esk1_0,esk2_0)
      | r2_hidden(esk1_0,k1_relat_1(k7_relat_1(esk3_0,esk2_0))) )
    & ( r2_hidden(esk1_0,k1_relat_1(esk3_0))
      | r2_hidden(esk1_0,k1_relat_1(k7_relat_1(esk3_0,esk2_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_relat_1(k7_relat_1(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ v1_relat_1(X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_10])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,esk6_3(X2,X3,X1)),k7_relat_1(X2,X4))
    | X3 != k1_relat_1(X2)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_10])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X4)))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(esk3_0))
    | r2_hidden(esk1_0,k1_relat_1(k7_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    | r2_hidden(esk1_0,k1_relat_1(k7_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_relat_1(k7_relat_1(X3,X4))
    | X5 != k1_relat_1(X3)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X5)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(esk3_0))
    | r2_hidden(esk1_0,X1)
    | X1 != k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(k7_relat_1(esk3_0,esk2_0)))
    | ~ r2_hidden(esk1_0,esk2_0)
    | ~ r2_hidden(esk1_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_24])])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | X4 != k1_relat_1(X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(esk3_0)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(k7_relat_1(esk3_0,esk2_0)))
    | ~ r2_hidden(esk1_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(k7_relat_1(X1,X2)))
    | k1_relat_1(esk3_0) != k1_relat_1(X1)
    | ~ r2_hidden(esk1_0,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(k7_relat_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_32])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(k7_relat_1(esk3_0,X1)))
    | ~ r2_hidden(esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_24])])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
