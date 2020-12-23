%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t72_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:04 EDT 2019

% Result     : Theorem 103.46s
% Output     : CNFRefutation 103.46s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 201 expanded)
%              Number of clauses        :   34 (  98 expanded)
%              Number of leaves         :    5 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  168 ( 897 expanded)
%              Number of equality atoms :   54 ( 260 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X2 = k4_relat_1(X1)
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t72_relat_1.p',d7_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t72_relat_1.p',dt_k4_relat_1)).

fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t72_relat_1.p',d10_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t72_relat_1.p',dt_k6_relat_1)).

fof(t72_relat_1,conjecture,(
    ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t72_relat_1.p',t72_relat_1)).

fof(c_0_5,plain,(
    ! [X24,X25,X26,X27,X28,X29] :
      ( ( ~ r2_hidden(k4_tarski(X26,X27),X25)
        | r2_hidden(k4_tarski(X27,X26),X24)
        | X25 != k4_relat_1(X24)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(X29,X28),X24)
        | r2_hidden(k4_tarski(X28,X29),X25)
        | X25 != k4_relat_1(X24)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(esk6_2(X24,X25),esk7_2(X24,X25)),X25)
        | ~ r2_hidden(k4_tarski(esk7_2(X24,X25),esk6_2(X24,X25)),X24)
        | X25 = k4_relat_1(X24)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk6_2(X24,X25),esk7_2(X24,X25)),X25)
        | r2_hidden(k4_tarski(esk7_2(X24,X25),esk6_2(X24,X25)),X24)
        | X25 = k4_relat_1(X24)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).

fof(c_0_6,plain,(
    ! [X32] :
      ( ~ v1_relat_1(X32)
      | v1_relat_1(k4_relat_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_7,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X10,X8)
        | ~ r2_hidden(k4_tarski(X10,X11),X9)
        | X9 != k6_relat_1(X8)
        | ~ v1_relat_1(X9) )
      & ( X10 = X11
        | ~ r2_hidden(k4_tarski(X10,X11),X9)
        | X9 != k6_relat_1(X8)
        | ~ v1_relat_1(X9) )
      & ( ~ r2_hidden(X12,X8)
        | X12 != X13
        | r2_hidden(k4_tarski(X12,X13),X9)
        | X9 != k6_relat_1(X8)
        | ~ v1_relat_1(X9) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X8,X9),esk3_2(X8,X9)),X9)
        | ~ r2_hidden(esk2_2(X8,X9),X8)
        | esk2_2(X8,X9) != esk3_2(X8,X9)
        | X9 = k6_relat_1(X8)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(esk2_2(X8,X9),X8)
        | r2_hidden(k4_tarski(esk2_2(X8,X9),esk3_2(X8,X9)),X9)
        | X9 = k6_relat_1(X8)
        | ~ v1_relat_1(X9) )
      & ( esk2_2(X8,X9) = esk3_2(X8,X9)
        | r2_hidden(k4_tarski(esk2_2(X8,X9),esk3_2(X8,X9)),X9)
        | X9 = k6_relat_1(X8)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(X2,X1),X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k4_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X33] : v1_relat_1(k6_relat_1(X33)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_11,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X2)
    | X2 = k6_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( X2 = k6_relat_1(X1)
    | ~ r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X2)
    | ~ r2_hidden(esk2_2(X1,X2),X1)
    | esk2_2(X1,X2) != esk3_2(X1,X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(X2,X1),X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k4_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( esk2_2(X1,X2) = esk3_2(X1,X2)
    | r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X2)
    | X2 = k6_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X2,X1),k4_relat_1(X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_8]),c_0_9])).

cnf(c_0_16,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k4_relat_1(X1) = k6_relat_1(X2)
    | r2_hidden(k4_tarski(esk2_2(X2,k4_relat_1(X1)),esk3_2(X2,k4_relat_1(X1))),k4_relat_1(X1))
    | r2_hidden(esk2_2(X2,k4_relat_1(X1)),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_9])).

cnf(c_0_18,plain,
    ( k4_relat_1(X1) = k6_relat_1(X2)
    | esk3_2(X2,k4_relat_1(X1)) != esk2_2(X2,k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(esk2_2(X2,k4_relat_1(X1)),esk3_2(X2,k4_relat_1(X1))),k4_relat_1(X1))
    | ~ r2_hidden(esk2_2(X2,k4_relat_1(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_9])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,X2),k4_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X2,X1),X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_9])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k6_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,plain,
    ( esk3_2(X1,k4_relat_1(X2)) = esk2_2(X1,k4_relat_1(X2))
    | k4_relat_1(X2) = k6_relat_1(X1)
    | r2_hidden(k4_tarski(esk2_2(X1,k4_relat_1(X2)),esk3_2(X1,k4_relat_1(X2))),k4_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_9])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,X2),k6_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X1),k4_relat_1(k6_relat_1(X3))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X2)
    | r2_hidden(k4_tarski(esk2_2(X2,k4_relat_1(k6_relat_1(X1))),esk3_2(X2,k4_relat_1(k6_relat_1(X1)))),k4_relat_1(k6_relat_1(X1)))
    | r2_hidden(esk2_2(X2,k4_relat_1(k6_relat_1(X1))),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_25,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X2)
    | esk3_2(X2,k4_relat_1(k6_relat_1(X1))) != esk2_2(X2,k4_relat_1(k6_relat_1(X1)))
    | ~ r2_hidden(k4_tarski(esk2_2(X2,k4_relat_1(k6_relat_1(X1))),esk3_2(X2,k4_relat_1(k6_relat_1(X1)))),k4_relat_1(k6_relat_1(X1)))
    | ~ r2_hidden(esk2_2(X2,k4_relat_1(k6_relat_1(X1))),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,X2),k4_relat_1(k6_relat_1(X3)))
    | ~ r2_hidden(k4_tarski(X2,X1),k6_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_16])).

cnf(c_0_27,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),k6_relat_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_20]),c_0_16])])).

cnf(c_0_28,plain,
    ( esk3_2(X1,k4_relat_1(k6_relat_1(X2))) = esk2_2(X1,k4_relat_1(k6_relat_1(X2)))
    | k4_relat_1(k6_relat_1(X2)) = k6_relat_1(X1)
    | r2_hidden(k4_tarski(esk2_2(X1,k4_relat_1(k6_relat_1(X2))),esk3_2(X1,k4_relat_1(k6_relat_1(X2)))),k4_relat_1(k6_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_16])])).

cnf(c_0_30,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X2)
    | r2_hidden(k4_tarski(esk3_2(X2,k4_relat_1(k6_relat_1(X1))),esk2_2(X2,k4_relat_1(k6_relat_1(X1)))),k6_relat_1(X1))
    | r2_hidden(esk2_2(X2,k4_relat_1(k6_relat_1(X1))),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X2)
    | ~ r2_hidden(k4_tarski(esk3_2(X2,k4_relat_1(k6_relat_1(X1))),esk2_2(X2,k4_relat_1(k6_relat_1(X1)))),k6_relat_1(X1))
    | ~ r2_hidden(esk2_2(X2,k4_relat_1(k6_relat_1(X1))),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_32,plain,
    ( esk3_2(X1,k4_relat_1(k6_relat_1(X2))) = esk2_2(X1,k4_relat_1(k6_relat_1(X2)))
    | k4_relat_1(k6_relat_1(X2)) = k6_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_28]),c_0_27])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2)
    | X1 != X3
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_34,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X2)
    | r2_hidden(esk2_2(X2,k4_relat_1(k6_relat_1(X1))),X2)
    | r2_hidden(esk3_2(X2,k4_relat_1(k6_relat_1(X1))),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_35,negated_conjecture,(
    ~ ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(assume_negation,[status(cth)],[t72_relat_1])).

cnf(c_0_36,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X2)
    | ~ r2_hidden(k4_tarski(esk2_2(X2,k4_relat_1(k6_relat_1(X1))),esk2_2(X2,k4_relat_1(k6_relat_1(X1)))),k6_relat_1(X1))
    | ~ r2_hidden(esk2_2(X2,k4_relat_1(k6_relat_1(X1))),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X1,X1),k6_relat_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])]),c_0_16])])).

cnf(c_0_38,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X2)
    | r2_hidden(esk2_2(X2,k4_relat_1(k6_relat_1(X1))),X1)
    | r2_hidden(esk2_2(X2,k4_relat_1(k6_relat_1(X1))),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_32])).

fof(c_0_39,negated_conjecture,(
    k4_relat_1(k6_relat_1(esk1_0)) != k6_relat_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).

cnf(c_0_40,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X2)
    | ~ r2_hidden(esk2_2(X2,k4_relat_1(k6_relat_1(X1))),X2)
    | ~ r2_hidden(esk2_2(X2,k4_relat_1(k6_relat_1(X1))),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1)
    | r2_hidden(esk2_2(X1,k4_relat_1(k6_relat_1(X1))),X1) ),
    inference(ef,[status(thm)],[c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( k4_relat_1(k6_relat_1(esk1_0)) != k6_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])]),
    [proof]).
%------------------------------------------------------------------------------
