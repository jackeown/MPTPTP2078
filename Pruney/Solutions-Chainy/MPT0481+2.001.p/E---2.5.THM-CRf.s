%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:25 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 136 expanded)
%              Number of clauses        :   29 (  59 expanded)
%              Number of leaves         :    6 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  186 ( 579 expanded)
%              Number of equality atoms :   26 (  64 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(t76_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X9,X7)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k6_relat_1(X7)
        | ~ v1_relat_1(X8) )
      & ( X9 = X10
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k6_relat_1(X7)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(X11,X7)
        | X11 != X12
        | r2_hidden(k4_tarski(X11,X12),X8)
        | X8 != k6_relat_1(X7)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)
        | ~ r2_hidden(esk1_2(X7,X8),X7)
        | esk1_2(X7,X8) != esk2_2(X7,X8)
        | X8 = k6_relat_1(X7)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)
        | X8 = k6_relat_1(X7)
        | ~ v1_relat_1(X8) )
      & ( esk1_2(X7,X8) = esk2_2(X7,X8)
        | r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)
        | X8 = k6_relat_1(X7)
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

fof(c_0_7,plain,(
    ! [X37] : v1_relat_1(k6_relat_1(X37)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_8,plain,(
    ! [X22,X23,X24,X25,X26,X28,X29,X30,X33] :
      ( ( r2_hidden(k4_tarski(X25,esk5_5(X22,X23,X24,X25,X26)),X22)
        | ~ r2_hidden(k4_tarski(X25,X26),X24)
        | X24 != k5_relat_1(X22,X23)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(k4_tarski(esk5_5(X22,X23,X24,X25,X26),X26),X23)
        | ~ r2_hidden(k4_tarski(X25,X26),X24)
        | X24 != k5_relat_1(X22,X23)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(X28,X30),X22)
        | ~ r2_hidden(k4_tarski(X30,X29),X23)
        | r2_hidden(k4_tarski(X28,X29),X24)
        | X24 != k5_relat_1(X22,X23)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(esk6_3(X22,X23,X24),esk7_3(X22,X23,X24)),X24)
        | ~ r2_hidden(k4_tarski(esk6_3(X22,X23,X24),X33),X22)
        | ~ r2_hidden(k4_tarski(X33,esk7_3(X22,X23,X24)),X23)
        | X24 = k5_relat_1(X22,X23)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(k4_tarski(esk6_3(X22,X23,X24),esk8_3(X22,X23,X24)),X22)
        | r2_hidden(k4_tarski(esk6_3(X22,X23,X24),esk7_3(X22,X23,X24)),X24)
        | X24 = k5_relat_1(X22,X23)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(k4_tarski(esk8_3(X22,X23,X24),esk7_3(X22,X23,X24)),X23)
        | r2_hidden(k4_tarski(esk6_3(X22,X23,X24),esk7_3(X22,X23,X24)),X24)
        | X24 = k5_relat_1(X22,X23)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_9,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X35)
      | ~ v1_relat_1(X36)
      | v1_relat_1(k5_relat_1(X35,X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_10,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( ~ r1_tarski(X15,X16)
        | ~ r2_hidden(k4_tarski(X17,X18),X15)
        | r2_hidden(k4_tarski(X17,X18),X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk3_2(X15,X19),esk4_2(X15,X19)),X15)
        | r1_tarski(X15,X19)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X15,X19),esk4_2(X15,X19)),X19)
        | r1_tarski(X15,X19)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
          & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t76_relat_1])).

cnf(c_0_12,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k6_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,esk5_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & ( ~ r1_tarski(k5_relat_1(esk10_0,k6_relat_1(esk9_0)),esk10_0)
      | ~ r1_tarski(k5_relat_1(k6_relat_1(esk9_0),esk10_0),esk10_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(esk5_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),k6_relat_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_13])])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,esk5_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(k5_relat_1(X1,X2),X3)
    | r2_hidden(k4_tarski(esk3_2(k5_relat_1(X1,X2),X3),esk4_2(k5_relat_1(X1,X2),X3)),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(esk5_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]),c_0_15])).

cnf(c_0_24,plain,
    ( esk5_5(k6_relat_1(X1),X2,k5_relat_1(k6_relat_1(X1),X2),X3,X4) = X3
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(k6_relat_1(X1),X2))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_13])])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,esk10_0),X2)
    | r2_hidden(k4_tarski(esk3_2(k5_relat_1(X1,esk10_0),X2),esk4_2(k5_relat_1(X1,esk10_0),X2)),k5_relat_1(X1,esk10_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X4),X3))
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_13])])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),esk10_0),X2)
    | r2_hidden(k4_tarski(esk3_2(k5_relat_1(k6_relat_1(X1),esk10_0),X2),esk4_2(k5_relat_1(k6_relat_1(X1),esk10_0),X2)),k5_relat_1(k6_relat_1(X1),esk10_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_13])).

cnf(c_0_28,plain,
    ( esk5_5(X1,k6_relat_1(X2),k5_relat_1(X1,k6_relat_1(X2)),X3,X4) = X4
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,k6_relat_1(X2)))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_23]),c_0_13])])).

cnf(c_0_29,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X3)
    | r2_hidden(k4_tarski(esk3_2(k5_relat_1(X1,k6_relat_1(X2)),X3),esk4_2(k5_relat_1(X1,k6_relat_1(X2)),X3)),k5_relat_1(X1,k6_relat_1(X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_13])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),esk10_0),X2)
    | r2_hidden(k4_tarski(esk3_2(k5_relat_1(k6_relat_1(X1),esk10_0),X2),esk4_2(k5_relat_1(k6_relat_1(X1),esk10_0),X2)),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_22])])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,k6_relat_1(X4)))
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_28]),c_0_13])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk10_0,k6_relat_1(X1)),X2)
    | r2_hidden(k4_tarski(esk3_2(k5_relat_1(esk10_0,k6_relat_1(X1)),X2),esk4_2(k5_relat_1(esk10_0,k6_relat_1(X1)),X2)),k5_relat_1(esk10_0,k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk10_0,k6_relat_1(esk9_0)),esk10_0)
    | ~ r1_tarski(k5_relat_1(k6_relat_1(esk9_0),esk10_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),esk10_0),esk10_0)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),esk10_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk10_0,k6_relat_1(X1)),X2)
    | r2_hidden(k4_tarski(esk3_2(k5_relat_1(esk10_0,k6_relat_1(X1)),X2),esk4_2(k5_relat_1(esk10_0,k6_relat_1(X1)),X2)),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_22])])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk10_0,k6_relat_1(esk9_0)),esk10_0)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(esk9_0),esk10_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk10_0,k6_relat_1(X1)),esk10_0)
    | ~ v1_relat_1(k5_relat_1(esk10_0,k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(esk9_0),esk10_0))
    | ~ v1_relat_1(k5_relat_1(esk10_0,k6_relat_1(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_relat_1(k5_relat_1(esk10_0,k6_relat_1(esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_15]),c_0_22]),c_0_13])])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_15]),c_0_13]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.49  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.49  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.49  #
% 0.19/0.49  # Preprocessing time       : 0.029 s
% 0.19/0.49  # Presaturation interreduction done
% 0.19/0.49  
% 0.19/0.49  # Proof found!
% 0.19/0.49  # SZS status Theorem
% 0.19/0.49  # SZS output start CNFRefutation
% 0.19/0.49  fof(d10_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k6_relat_1(X1)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X2)<=>(r2_hidden(X3,X1)&X3=X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 0.19/0.49  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.19/0.49  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 0.19/0.49  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.19/0.49  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 0.19/0.49  fof(t76_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 0.19/0.49  fof(c_0_6, plain, ![X7, X8, X9, X10, X11, X12]:((((r2_hidden(X9,X7)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k6_relat_1(X7)|~v1_relat_1(X8))&(X9=X10|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k6_relat_1(X7)|~v1_relat_1(X8)))&(~r2_hidden(X11,X7)|X11!=X12|r2_hidden(k4_tarski(X11,X12),X8)|X8!=k6_relat_1(X7)|~v1_relat_1(X8)))&((~r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)|(~r2_hidden(esk1_2(X7,X8),X7)|esk1_2(X7,X8)!=esk2_2(X7,X8))|X8=k6_relat_1(X7)|~v1_relat_1(X8))&((r2_hidden(esk1_2(X7,X8),X7)|r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)|X8=k6_relat_1(X7)|~v1_relat_1(X8))&(esk1_2(X7,X8)=esk2_2(X7,X8)|r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)|X8=k6_relat_1(X7)|~v1_relat_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).
% 0.19/0.49  fof(c_0_7, plain, ![X37]:v1_relat_1(k6_relat_1(X37)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.19/0.49  fof(c_0_8, plain, ![X22, X23, X24, X25, X26, X28, X29, X30, X33]:((((r2_hidden(k4_tarski(X25,esk5_5(X22,X23,X24,X25,X26)),X22)|~r2_hidden(k4_tarski(X25,X26),X24)|X24!=k5_relat_1(X22,X23)|~v1_relat_1(X24)|~v1_relat_1(X23)|~v1_relat_1(X22))&(r2_hidden(k4_tarski(esk5_5(X22,X23,X24,X25,X26),X26),X23)|~r2_hidden(k4_tarski(X25,X26),X24)|X24!=k5_relat_1(X22,X23)|~v1_relat_1(X24)|~v1_relat_1(X23)|~v1_relat_1(X22)))&(~r2_hidden(k4_tarski(X28,X30),X22)|~r2_hidden(k4_tarski(X30,X29),X23)|r2_hidden(k4_tarski(X28,X29),X24)|X24!=k5_relat_1(X22,X23)|~v1_relat_1(X24)|~v1_relat_1(X23)|~v1_relat_1(X22)))&((~r2_hidden(k4_tarski(esk6_3(X22,X23,X24),esk7_3(X22,X23,X24)),X24)|(~r2_hidden(k4_tarski(esk6_3(X22,X23,X24),X33),X22)|~r2_hidden(k4_tarski(X33,esk7_3(X22,X23,X24)),X23))|X24=k5_relat_1(X22,X23)|~v1_relat_1(X24)|~v1_relat_1(X23)|~v1_relat_1(X22))&((r2_hidden(k4_tarski(esk6_3(X22,X23,X24),esk8_3(X22,X23,X24)),X22)|r2_hidden(k4_tarski(esk6_3(X22,X23,X24),esk7_3(X22,X23,X24)),X24)|X24=k5_relat_1(X22,X23)|~v1_relat_1(X24)|~v1_relat_1(X23)|~v1_relat_1(X22))&(r2_hidden(k4_tarski(esk8_3(X22,X23,X24),esk7_3(X22,X23,X24)),X23)|r2_hidden(k4_tarski(esk6_3(X22,X23,X24),esk7_3(X22,X23,X24)),X24)|X24=k5_relat_1(X22,X23)|~v1_relat_1(X24)|~v1_relat_1(X23)|~v1_relat_1(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.19/0.49  fof(c_0_9, plain, ![X35, X36]:(~v1_relat_1(X35)|~v1_relat_1(X36)|v1_relat_1(k5_relat_1(X35,X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.19/0.49  fof(c_0_10, plain, ![X15, X16, X17, X18, X19]:((~r1_tarski(X15,X16)|(~r2_hidden(k4_tarski(X17,X18),X15)|r2_hidden(k4_tarski(X17,X18),X16))|~v1_relat_1(X15))&((r2_hidden(k4_tarski(esk3_2(X15,X19),esk4_2(X15,X19)),X15)|r1_tarski(X15,X19)|~v1_relat_1(X15))&(~r2_hidden(k4_tarski(esk3_2(X15,X19),esk4_2(X15,X19)),X19)|r1_tarski(X15,X19)|~v1_relat_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.19/0.49  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)))), inference(assume_negation,[status(cth)],[t76_relat_1])).
% 0.19/0.49  cnf(c_0_12, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X2),X3)|X3!=k6_relat_1(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.49  cnf(c_0_13, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.49  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,esk5_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.49  cnf(c_0_15, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.49  cnf(c_0_16, plain, (r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.49  fof(c_0_17, negated_conjecture, (v1_relat_1(esk10_0)&(~r1_tarski(k5_relat_1(esk10_0,k6_relat_1(esk9_0)),esk10_0)|~r1_tarski(k5_relat_1(k6_relat_1(esk9_0),esk10_0),esk10_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.19/0.49  cnf(c_0_18, plain, (r2_hidden(k4_tarski(esk5_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.49  cnf(c_0_19, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X2),k6_relat_1(X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_12]), c_0_13])])).
% 0.19/0.49  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X1,esk5_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)|~r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]), c_0_15])).
% 0.19/0.49  cnf(c_0_21, plain, (r1_tarski(k5_relat_1(X1,X2),X3)|r2_hidden(k4_tarski(esk3_2(k5_relat_1(X1,X2),X3),esk4_2(k5_relat_1(X1,X2),X3)),k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_15])).
% 0.19/0.49  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.49  cnf(c_0_23, plain, (r2_hidden(k4_tarski(esk5_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]), c_0_15])).
% 0.19/0.49  cnf(c_0_24, plain, (esk5_5(k6_relat_1(X1),X2,k5_relat_1(k6_relat_1(X1),X2),X3,X4)=X3|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(k6_relat_1(X1),X2))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_13])])).
% 0.19/0.49  cnf(c_0_25, negated_conjecture, (r1_tarski(k5_relat_1(X1,esk10_0),X2)|r2_hidden(k4_tarski(esk3_2(k5_relat_1(X1,esk10_0),X2),esk4_2(k5_relat_1(X1,esk10_0),X2)),k5_relat_1(X1,esk10_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.49  cnf(c_0_26, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X4),X3))|~v1_relat_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_13])])).
% 0.19/0.49  cnf(c_0_27, negated_conjecture, (r1_tarski(k5_relat_1(k6_relat_1(X1),esk10_0),X2)|r2_hidden(k4_tarski(esk3_2(k5_relat_1(k6_relat_1(X1),esk10_0),X2),esk4_2(k5_relat_1(k6_relat_1(X1),esk10_0),X2)),k5_relat_1(k6_relat_1(X1),esk10_0))), inference(spm,[status(thm)],[c_0_25, c_0_13])).
% 0.19/0.49  cnf(c_0_28, plain, (esk5_5(X1,k6_relat_1(X2),k5_relat_1(X1,k6_relat_1(X2)),X3,X4)=X4|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,k6_relat_1(X2)))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_23]), c_0_13])])).
% 0.19/0.49  cnf(c_0_29, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X3)|r2_hidden(k4_tarski(esk3_2(k5_relat_1(X1,k6_relat_1(X2)),X3),esk4_2(k5_relat_1(X1,k6_relat_1(X2)),X3)),k5_relat_1(X1,k6_relat_1(X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_13])).
% 0.19/0.49  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.49  cnf(c_0_31, negated_conjecture, (r1_tarski(k5_relat_1(k6_relat_1(X1),esk10_0),X2)|r2_hidden(k4_tarski(esk3_2(k5_relat_1(k6_relat_1(X1),esk10_0),X2),esk4_2(k5_relat_1(k6_relat_1(X1),esk10_0),X2)),esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_22])])).
% 0.19/0.49  cnf(c_0_32, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,k6_relat_1(X4)))|~v1_relat_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_28]), c_0_13])])).
% 0.19/0.49  cnf(c_0_33, negated_conjecture, (r1_tarski(k5_relat_1(esk10_0,k6_relat_1(X1)),X2)|r2_hidden(k4_tarski(esk3_2(k5_relat_1(esk10_0,k6_relat_1(X1)),X2),esk4_2(k5_relat_1(esk10_0,k6_relat_1(X1)),X2)),k5_relat_1(esk10_0,k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_29, c_0_22])).
% 0.19/0.49  cnf(c_0_34, negated_conjecture, (~r1_tarski(k5_relat_1(esk10_0,k6_relat_1(esk9_0)),esk10_0)|~r1_tarski(k5_relat_1(k6_relat_1(esk9_0),esk10_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.49  cnf(c_0_35, negated_conjecture, (r1_tarski(k5_relat_1(k6_relat_1(X1),esk10_0),esk10_0)|~v1_relat_1(k5_relat_1(k6_relat_1(X1),esk10_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.49  cnf(c_0_36, negated_conjecture, (r1_tarski(k5_relat_1(esk10_0,k6_relat_1(X1)),X2)|r2_hidden(k4_tarski(esk3_2(k5_relat_1(esk10_0,k6_relat_1(X1)),X2),esk4_2(k5_relat_1(esk10_0,k6_relat_1(X1)),X2)),esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_22])])).
% 0.19/0.49  cnf(c_0_37, negated_conjecture, (~r1_tarski(k5_relat_1(esk10_0,k6_relat_1(esk9_0)),esk10_0)|~v1_relat_1(k5_relat_1(k6_relat_1(esk9_0),esk10_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.49  cnf(c_0_38, negated_conjecture, (r1_tarski(k5_relat_1(esk10_0,k6_relat_1(X1)),esk10_0)|~v1_relat_1(k5_relat_1(esk10_0,k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_30, c_0_36])).
% 0.19/0.49  cnf(c_0_39, negated_conjecture, (~v1_relat_1(k5_relat_1(k6_relat_1(esk9_0),esk10_0))|~v1_relat_1(k5_relat_1(esk10_0,k6_relat_1(esk9_0)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.49  cnf(c_0_40, negated_conjecture, (~v1_relat_1(k5_relat_1(esk10_0,k6_relat_1(esk9_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_15]), c_0_22]), c_0_13])])).
% 0.19/0.49  cnf(c_0_41, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_15]), c_0_13]), c_0_22])]), ['proof']).
% 0.19/0.49  # SZS output end CNFRefutation
% 0.19/0.49  # Proof object total steps             : 42
% 0.19/0.49  # Proof object clause steps            : 29
% 0.19/0.49  # Proof object formula steps           : 13
% 0.19/0.49  # Proof object conjectures             : 16
% 0.19/0.49  # Proof object clause conjectures      : 13
% 0.19/0.49  # Proof object formula conjectures     : 3
% 0.19/0.49  # Proof object initial clauses used    : 9
% 0.19/0.49  # Proof object initial formulas used   : 6
% 0.19/0.49  # Proof object generating inferences   : 17
% 0.19/0.49  # Proof object simplifying inferences  : 25
% 0.19/0.49  # Training examples: 0 positive, 0 negative
% 0.19/0.49  # Parsed axioms                        : 6
% 0.19/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.49  # Initial clauses                      : 19
% 0.19/0.49  # Removed in clause preprocessing      : 0
% 0.19/0.49  # Initial clauses in saturation        : 19
% 0.19/0.49  # Processed clauses                    : 796
% 0.19/0.49  # ...of these trivial                  : 0
% 0.19/0.49  # ...subsumed                          : 370
% 0.19/0.49  # ...remaining for further processing  : 426
% 0.19/0.49  # Other redundant clauses eliminated   : 7
% 0.19/0.49  # Clauses deleted for lack of memory   : 0
% 0.19/0.49  # Backward-subsumed                    : 21
% 0.19/0.49  # Backward-rewritten                   : 0
% 0.19/0.49  # Generated clauses                    : 2778
% 0.19/0.49  # ...of the previous two non-trivial   : 2702
% 0.19/0.49  # Contextual simplify-reflections      : 13
% 0.19/0.49  # Paramodulations                      : 2770
% 0.19/0.49  # Factorizations                       : 2
% 0.19/0.49  # Equation resolutions                 : 7
% 0.19/0.49  # Propositional unsat checks           : 0
% 0.19/0.49  #    Propositional check models        : 0
% 0.19/0.49  #    Propositional check unsatisfiable : 0
% 0.19/0.49  #    Propositional clauses             : 0
% 0.19/0.49  #    Propositional clauses after purity: 0
% 0.19/0.49  #    Propositional unsat core size     : 0
% 0.19/0.49  #    Propositional preprocessing time  : 0.000
% 0.19/0.49  #    Propositional encoding time       : 0.000
% 0.19/0.49  #    Propositional solver time         : 0.000
% 0.19/0.49  #    Success case prop preproc time    : 0.000
% 0.19/0.49  #    Success case prop encoding time   : 0.000
% 0.19/0.49  #    Success case prop solver time     : 0.000
% 0.19/0.49  # Current number of processed clauses  : 380
% 0.19/0.49  #    Positive orientable unit clauses  : 5
% 0.19/0.49  #    Positive unorientable unit clauses: 0
% 0.19/0.49  #    Negative unit clauses             : 1
% 0.19/0.49  #    Non-unit-clauses                  : 374
% 0.19/0.49  # Current number of unprocessed clauses: 1943
% 0.19/0.49  # ...number of literals in the above   : 12740
% 0.19/0.49  # Current number of archived formulas  : 0
% 0.19/0.49  # Current number of archived clauses   : 40
% 0.19/0.49  # Clause-clause subsumption calls (NU) : 28258
% 0.19/0.49  # Rec. Clause-clause subsumption calls : 6490
% 0.19/0.49  # Non-unit clause-clause subsumptions  : 404
% 0.19/0.49  # Unit Clause-clause subsumption calls : 96
% 0.19/0.49  # Rewrite failures with RHS unbound    : 0
% 0.19/0.49  # BW rewrite match attempts            : 0
% 0.19/0.49  # BW rewrite match successes           : 0
% 0.19/0.49  # Condensation attempts                : 0
% 0.19/0.49  # Condensation successes               : 0
% 0.19/0.49  # Termbank termtop insertions          : 90562
% 0.19/0.49  
% 0.19/0.49  # -------------------------------------------------
% 0.19/0.49  # User time                : 0.142 s
% 0.19/0.49  # System time              : 0.005 s
% 0.19/0.49  # Total time               : 0.147 s
% 0.19/0.49  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
