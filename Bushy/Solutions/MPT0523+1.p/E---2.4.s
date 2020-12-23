%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t123_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:48 EDT 2019

% Result     : Theorem 264.80s
% Output     : CNFRefutation 264.80s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 152 expanded)
%              Number of clauses        :   27 (  64 expanded)
%              Number of leaves         :    5 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  151 ( 566 expanded)
%              Number of equality atoms :   30 ( 116 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t123_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t123_relat_1.p',t123_relat_1)).

fof(d12_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( X3 = k8_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t123_relat_1.p',d12_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t123_relat_1.p',dt_k5_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t123_relat_1.p',dt_k6_relat_1)).

fof(t75_relat_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X4,k6_relat_1(X3)))
      <=> ( r2_hidden(X2,X3)
          & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t123_relat_1.p',t75_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    inference(assume_negation,[status(cth)],[t123_relat_1])).

fof(c_0_6,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X14,X10)
        | ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X12 != k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(X13,X14),X11)
        | ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X12 != k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(X16,X10)
        | ~ r2_hidden(k4_tarski(X15,X16),X11)
        | r2_hidden(k4_tarski(X15,X16),X12)
        | X12 != k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk3_3(X10,X11,X12),esk4_3(X10,X11,X12)),X12)
        | ~ r2_hidden(esk4_3(X10,X11,X12),X10)
        | ~ r2_hidden(k4_tarski(esk3_3(X10,X11,X12),esk4_3(X10,X11,X12)),X11)
        | X12 = k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk4_3(X10,X11,X12),X10)
        | r2_hidden(k4_tarski(esk3_3(X10,X11,X12),esk4_3(X10,X11,X12)),X12)
        | X12 = k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk3_3(X10,X11,X12),esk4_3(X10,X11,X12)),X11)
        | r2_hidden(k4_tarski(esk3_3(X10,X11,X12),esk4_3(X10,X11,X12)),X12)
        | X12 = k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & k8_relat_1(esk1_0,esk2_0) != k5_relat_1(esk2_0,k6_relat_1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_8,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X1)
    | r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk4_3(X1,X2,X3)),X3)
    | X3 = k8_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X27)
      | ~ v1_relat_1(X28)
      | v1_relat_1(k5_relat_1(X27,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_11,negated_conjecture,
    ( X1 = k8_relat_1(X2,esk2_0)
    | r2_hidden(k4_tarski(esk3_3(X2,esk2_0,X1),esk4_3(X2,esk2_0,X1)),X1)
    | r2_hidden(esk4_3(X2,esk2_0,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( k5_relat_1(X1,X2) = k8_relat_1(X3,esk2_0)
    | r2_hidden(k4_tarski(esk3_3(X3,esk2_0,k5_relat_1(X1,X2)),esk4_3(X3,esk2_0,k5_relat_1(X1,X2))),k5_relat_1(X1,X2))
    | r2_hidden(esk4_3(X3,esk2_0,k5_relat_1(X1,X2)),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_14,plain,(
    ! [X29] : v1_relat_1(k6_relat_1(X29)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_15,plain,(
    ! [X39,X40,X41,X42] :
      ( ( r2_hidden(X40,X41)
        | ~ r2_hidden(k4_tarski(X39,X40),k5_relat_1(X42,k6_relat_1(X41)))
        | ~ v1_relat_1(X42) )
      & ( r2_hidden(k4_tarski(X39,X40),X42)
        | ~ r2_hidden(k4_tarski(X39,X40),k5_relat_1(X42,k6_relat_1(X41)))
        | ~ v1_relat_1(X42) )
      & ( ~ r2_hidden(X40,X41)
        | ~ r2_hidden(k4_tarski(X39,X40),X42)
        | r2_hidden(k4_tarski(X39,X40),k5_relat_1(X42,k6_relat_1(X41)))
        | ~ v1_relat_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t75_relat_1])])])).

cnf(c_0_16,negated_conjecture,
    ( k5_relat_1(esk2_0,X1) = k8_relat_1(X2,esk2_0)
    | r2_hidden(k4_tarski(esk3_3(X2,esk2_0,k5_relat_1(esk2_0,X1)),esk4_3(X2,esk2_0,k5_relat_1(esk2_0,X1))),k5_relat_1(esk2_0,X1))
    | r2_hidden(esk4_3(X2,esk2_0,k5_relat_1(esk2_0,X1)),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_9])).

cnf(c_0_17,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk4_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk4_3(X1,X2,X3)),X3)
    | X3 = k8_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,k6_relat_1(X2)))
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(X1)) = k8_relat_1(X2,esk2_0)
    | r2_hidden(k4_tarski(esk3_3(X2,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),esk4_3(X2,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1)))),k5_relat_1(esk2_0,k6_relat_1(X1)))
    | r2_hidden(esk4_3(X2,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( X1 = k8_relat_1(X2,esk2_0)
    | r2_hidden(k4_tarski(esk3_3(X2,esk2_0,X1),esk4_3(X2,esk2_0,X1)),esk2_0)
    | r2_hidden(k4_tarski(esk3_3(X2,esk2_0,X1),esk4_3(X2,esk2_0,X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(X1)) = k8_relat_1(X2,esk2_0)
    | r2_hidden(esk4_3(X2,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),X2)
    | r2_hidden(esk4_3(X2,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_9])])).

cnf(c_0_23,negated_conjecture,
    ( k5_relat_1(X1,X2) = k8_relat_1(X3,esk2_0)
    | r2_hidden(k4_tarski(esk3_3(X3,esk2_0,k5_relat_1(X1,X2)),esk4_3(X3,esk2_0,k5_relat_1(X1,X2))),k5_relat_1(X1,X2))
    | r2_hidden(k4_tarski(esk3_3(X3,esk2_0,k5_relat_1(X1,X2)),esk4_3(X3,esk2_0,k5_relat_1(X1,X2))),esk2_0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_12])).

cnf(c_0_24,plain,
    ( X3 = k8_relat_1(X1,X2)
    | ~ r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk4_3(X1,X2,X3)),X3)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X1)
    | ~ r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk4_3(X1,X2,X3)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(X1)) = k8_relat_1(X1,esk2_0)
    | r2_hidden(esk4_3(X1,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),X1) ),
    inference(ef,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( k5_relat_1(esk2_0,X1) = k8_relat_1(X2,esk2_0)
    | r2_hidden(k4_tarski(esk3_3(X2,esk2_0,k5_relat_1(esk2_0,X1)),esk4_3(X2,esk2_0,k5_relat_1(esk2_0,X1))),k5_relat_1(esk2_0,X1))
    | r2_hidden(k4_tarski(esk3_3(X2,esk2_0,k5_relat_1(esk2_0,X1)),esk4_3(X2,esk2_0,k5_relat_1(esk2_0,X1))),esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(X1)) = k8_relat_1(X1,esk2_0)
    | ~ r2_hidden(k4_tarski(esk3_3(X1,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),esk4_3(X1,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1)))),k5_relat_1(esk2_0,k6_relat_1(X1)))
    | ~ r2_hidden(k4_tarski(esk3_3(X1,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),esk4_3(X1,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1)))),esk2_0)
    | ~ v1_relat_1(k5_relat_1(esk2_0,k6_relat_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_9])])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,k6_relat_1(X4)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(X1)) = k8_relat_1(X2,esk2_0)
    | r2_hidden(k4_tarski(esk3_3(X2,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),esk4_3(X2,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1)))),k5_relat_1(esk2_0,k6_relat_1(X1)))
    | r2_hidden(k4_tarski(esk3_3(X2,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),esk4_3(X2,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1)))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(X1)) = k8_relat_1(X1,esk2_0)
    | ~ r2_hidden(k4_tarski(esk3_3(X1,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),esk4_3(X1,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1)))),k5_relat_1(esk2_0,k6_relat_1(X1)))
    | ~ r2_hidden(k4_tarski(esk3_3(X1,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),esk4_3(X1,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1)))),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_12]),c_0_17]),c_0_9])])).

cnf(c_0_31,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(X1)) = k8_relat_1(X2,esk2_0)
    | r2_hidden(k4_tarski(esk3_3(X2,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),esk4_3(X2,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1)))),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_9])])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,k6_relat_1(X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(X1)) = k8_relat_1(X1,esk2_0)
    | ~ r2_hidden(k4_tarski(esk3_3(X1,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),esk4_3(X1,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1)))),k5_relat_1(esk2_0,k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(X1)) = k8_relat_1(X2,esk2_0)
    | r2_hidden(k4_tarski(esk3_3(X2,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),esk4_3(X2,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1)))),k5_relat_1(esk2_0,k6_relat_1(X3)))
    | ~ r2_hidden(esk4_3(X2,esk2_0,k5_relat_1(esk2_0,k6_relat_1(X1))),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_31]),c_0_9])])).

cnf(c_0_35,negated_conjecture,
    ( k8_relat_1(esk1_0,esk2_0) != k5_relat_1(esk2_0,k6_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(X1)) = k8_relat_1(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
