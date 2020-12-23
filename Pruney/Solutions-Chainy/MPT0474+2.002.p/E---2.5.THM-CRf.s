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
% DateTime   : Thu Dec  3 10:49:22 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 261 expanded)
%              Number of clauses        :   34 ( 124 expanded)
%              Number of leaves         :    9 (  74 expanded)
%              Depth                    :   16
%              Number of atoms          :  176 ( 807 expanded)
%              Number of equality atoms :   25 (  81 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(d7_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X2 = k4_relat_1(X1)
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(involutiveness_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k4_relat_1(k4_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X1 = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X1)
              <=> r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).

fof(t66_relat_1,conjecture,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

fof(c_0_9,plain,(
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

fof(c_0_10,plain,(
    ! [X30] :
      ( ~ v1_relat_1(X30)
      | v1_relat_1(k4_relat_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_11,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(k4_tarski(X24,X25),X23)
        | r2_hidden(k4_tarski(X25,X24),X22)
        | X23 != k4_relat_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(X27,X26),X22)
        | r2_hidden(k4_tarski(X26,X27),X23)
        | X23 != k4_relat_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(esk5_2(X22,X23),esk6_2(X22,X23)),X23)
        | ~ r2_hidden(k4_tarski(esk6_2(X22,X23),esk5_2(X22,X23)),X22)
        | X23 = k4_relat_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(k4_tarski(esk5_2(X22,X23),esk6_2(X22,X23)),X23)
        | r2_hidden(k4_tarski(esk6_2(X22,X23),esk5_2(X22,X23)),X22)
        | X23 = k4_relat_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(X6)
      | v1_relat_1(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X2,X1),X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k4_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(esk3_2(k4_relat_1(X1),X2),esk4_2(k4_relat_1(X1),X2)),k4_relat_1(X1))
    | r1_tarski(k4_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X3,X4),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,X2),k4_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X1),X3)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_15]),c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk3_2(k4_relat_1(k4_relat_1(X1)),X2),esk4_2(k4_relat_1(k4_relat_1(X1)),X2)),k4_relat_1(k4_relat_1(X1)))
    | r1_tarski(k4_relat_1(k4_relat_1(X1)),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_13])).

cnf(c_0_22,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X1),X4)
    | ~ v1_relat_1(X4)
    | ~ r1_tarski(k4_relat_1(X4),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_13])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(esk3_2(k4_relat_1(k4_relat_1(k1_xboole_0)),X1),esk4_2(k4_relat_1(k4_relat_1(k1_xboole_0)),X1)),k4_relat_1(k4_relat_1(k1_xboole_0)))
    | r1_tarski(k4_relat_1(k4_relat_1(k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | ~ v1_relat_1(X4)
    | ~ r1_tarski(k4_relat_1(k4_relat_1(X4)),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_20]),c_0_13])).

cnf(c_0_27,plain,
    ( r1_tarski(k4_relat_1(k4_relat_1(k1_xboole_0)),k4_relat_1(k4_relat_1(k1_xboole_0)))
    | ~ v1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X1,X2),k4_relat_1(k4_relat_1(k1_xboole_0)))
    | ~ r2_hidden(k4_tarski(X1,X2),k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_22])])).

fof(c_0_29,plain,(
    ! [X31] :
      ( ~ v1_relat_1(X31)
      | k4_relat_1(k4_relat_1(X31)) = X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).

fof(c_0_30,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_31,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(k4_tarski(X9,X10),X7)
        | r2_hidden(k4_tarski(X9,X10),X8)
        | X7 != X8
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(X11,X12),X8)
        | r2_hidden(k4_tarski(X11,X12),X7)
        | X7 != X8
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X7)
        | ~ r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)
        | X7 = X8
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X7)
        | r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)
        | X7 = X8
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_relat_1])])])])])])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))
    | ~ r1_tarski(k4_relat_1(k4_relat_1(k1_xboole_0)),X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_28])).

cnf(c_0_33,plain,
    ( k4_relat_1(k4_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | X1 = X2
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_22]),c_0_34])])).

fof(c_0_37,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t66_relat_1])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_2(X1,k1_xboole_0),esk2_2(X1,k1_xboole_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_22]),c_0_36])).

fof(c_0_39,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_simplification,[status(thm)],[c_0_37])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(X2,X1),X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k4_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_41,plain,
    ( k4_relat_1(X1) = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_2(k4_relat_1(X1),k1_xboole_0),esk2_2(k4_relat_1(X1),k1_xboole_0)),k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X1),k4_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]),c_0_13])).

cnf(c_0_45,plain,
    ( r2_hidden(k4_tarski(esk1_2(k4_relat_1(k1_xboole_0),k1_xboole_0),esk2_2(k4_relat_1(k1_xboole_0),k1_xboole_0)),k4_relat_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_22]),c_0_42])).

cnf(c_0_46,plain,
    ( X1 = k4_relat_1(X2)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,k4_relat_1(X2)),esk2_2(X1,k4_relat_1(X2))),X1)
    | ~ r2_hidden(k4_tarski(esk2_2(X1,k4_relat_1(X2)),esk1_2(X1,k4_relat_1(X2))),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_20]),c_0_13])).

cnf(c_0_47,plain,
    ( r2_hidden(k4_tarski(esk2_2(k4_relat_1(k1_xboole_0),k1_xboole_0),esk1_2(k4_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_22])])).

cnf(c_0_48,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(esk2_2(X1,X2),esk1_2(X1,X2)),k4_relat_1(X2))
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_33]),c_0_13])).

cnf(c_0_49,plain,
    ( r2_hidden(k4_tarski(esk2_2(k4_relat_1(k1_xboole_0),k1_xboole_0),esk1_2(k4_relat_1(k1_xboole_0),k1_xboole_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_47]),c_0_22]),c_0_34])])).

cnf(c_0_50,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_45]),c_0_22])]),c_0_42])).

cnf(c_0_51,plain,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_13]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:49:52 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.042 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 0.20/0.40  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 0.20/0.40  fof(d7_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(X2=k4_relat_1(X1)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X2)<=>r2_hidden(k4_tarski(X4,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_relat_1)).
% 0.20/0.40  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.20/0.40  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.40  fof(involutiveness_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k4_relat_1(k4_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 0.20/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.40  fof(d2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(X1=X2<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)<=>r2_hidden(k4_tarski(X3,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_relat_1)).
% 0.20/0.40  fof(t66_relat_1, conjecture, k4_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_relat_1)).
% 0.20/0.40  fof(c_0_9, plain, ![X15, X16, X17, X18, X19]:((~r1_tarski(X15,X16)|(~r2_hidden(k4_tarski(X17,X18),X15)|r2_hidden(k4_tarski(X17,X18),X16))|~v1_relat_1(X15))&((r2_hidden(k4_tarski(esk3_2(X15,X19),esk4_2(X15,X19)),X15)|r1_tarski(X15,X19)|~v1_relat_1(X15))&(~r2_hidden(k4_tarski(esk3_2(X15,X19),esk4_2(X15,X19)),X19)|r1_tarski(X15,X19)|~v1_relat_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.20/0.40  fof(c_0_10, plain, ![X30]:(~v1_relat_1(X30)|v1_relat_1(k4_relat_1(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 0.20/0.40  fof(c_0_11, plain, ![X22, X23, X24, X25, X26, X27]:(((~r2_hidden(k4_tarski(X24,X25),X23)|r2_hidden(k4_tarski(X25,X24),X22)|X23!=k4_relat_1(X22)|~v1_relat_1(X23)|~v1_relat_1(X22))&(~r2_hidden(k4_tarski(X27,X26),X22)|r2_hidden(k4_tarski(X26,X27),X23)|X23!=k4_relat_1(X22)|~v1_relat_1(X23)|~v1_relat_1(X22)))&((~r2_hidden(k4_tarski(esk5_2(X22,X23),esk6_2(X22,X23)),X23)|~r2_hidden(k4_tarski(esk6_2(X22,X23),esk5_2(X22,X23)),X22)|X23=k4_relat_1(X22)|~v1_relat_1(X23)|~v1_relat_1(X22))&(r2_hidden(k4_tarski(esk5_2(X22,X23),esk6_2(X22,X23)),X23)|r2_hidden(k4_tarski(esk6_2(X22,X23),esk5_2(X22,X23)),X22)|X23=k4_relat_1(X22)|~v1_relat_1(X23)|~v1_relat_1(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).
% 0.20/0.40  cnf(c_0_12, plain, (r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_13, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  fof(c_0_14, plain, ![X6]:(~v1_xboole_0(X6)|v1_relat_1(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.20/0.40  cnf(c_0_15, plain, (r2_hidden(k4_tarski(X2,X1),X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k4_relat_1(X3)|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_16, plain, (r2_hidden(k4_tarski(esk3_2(k4_relat_1(X1),X2),esk4_2(k4_relat_1(X1),X2)),k4_relat_1(X1))|r1_tarski(k4_relat_1(X1),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.40  cnf(c_0_17, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_18, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.40  cnf(c_0_19, plain, (r2_hidden(k4_tarski(X3,X4),X2)|~r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X1,X2),k4_relat_1(X3))|~r2_hidden(k4_tarski(X2,X1),X3)|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_15]), c_0_13])).
% 0.20/0.40  cnf(c_0_21, plain, (r2_hidden(k4_tarski(esk3_2(k4_relat_1(k4_relat_1(X1)),X2),esk4_2(k4_relat_1(k4_relat_1(X1)),X2)),k4_relat_1(k4_relat_1(X1)))|r1_tarski(k4_relat_1(k4_relat_1(X1)),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_13])).
% 0.20/0.40  cnf(c_0_22, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.40  cnf(c_0_23, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X2,X1),X4)|~v1_relat_1(X4)|~r1_tarski(k4_relat_1(X4),X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_13])).
% 0.20/0.40  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_25, plain, (r2_hidden(k4_tarski(esk3_2(k4_relat_1(k4_relat_1(k1_xboole_0)),X1),esk4_2(k4_relat_1(k4_relat_1(k1_xboole_0)),X1)),k4_relat_1(k4_relat_1(k1_xboole_0)))|r1_tarski(k4_relat_1(k4_relat_1(k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.40  cnf(c_0_26, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X1,X2),X4)|~v1_relat_1(X4)|~r1_tarski(k4_relat_1(k4_relat_1(X4)),X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_20]), c_0_13])).
% 0.20/0.40  cnf(c_0_27, plain, (r1_tarski(k4_relat_1(k4_relat_1(k1_xboole_0)),k4_relat_1(k4_relat_1(k1_xboole_0)))|~v1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.40  cnf(c_0_28, plain, (r2_hidden(k4_tarski(X1,X2),k4_relat_1(k4_relat_1(k1_xboole_0)))|~r2_hidden(k4_tarski(X1,X2),k1_xboole_0)|~v1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_22])])).
% 0.20/0.40  fof(c_0_29, plain, ![X31]:(~v1_relat_1(X31)|k4_relat_1(k4_relat_1(X31))=X31), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).
% 0.20/0.40  fof(c_0_30, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.40  fof(c_0_31, plain, ![X7, X8, X9, X10, X11, X12]:(((~r2_hidden(k4_tarski(X9,X10),X7)|r2_hidden(k4_tarski(X9,X10),X8)|X7!=X8|~v1_relat_1(X8)|~v1_relat_1(X7))&(~r2_hidden(k4_tarski(X11,X12),X8)|r2_hidden(k4_tarski(X11,X12),X7)|X7!=X8|~v1_relat_1(X8)|~v1_relat_1(X7)))&((~r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X7)|~r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)|X7=X8|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X7)|r2_hidden(k4_tarski(esk1_2(X7,X8),esk2_2(X7,X8)),X8)|X7=X8|~v1_relat_1(X8)|~v1_relat_1(X7)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_relat_1])])])])])])).
% 0.20/0.40  cnf(c_0_32, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X1,X2),k1_xboole_0)|~v1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))|~r1_tarski(k4_relat_1(k4_relat_1(k1_xboole_0)),X3)), inference(spm,[status(thm)],[c_0_19, c_0_28])).
% 0.20/0.40  cnf(c_0_33, plain, (k4_relat_1(k4_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.40  cnf(c_0_34, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_35, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|X1=X2|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.40  cnf(c_0_36, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X1,X2),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_22]), c_0_34])])).
% 0.20/0.40  fof(c_0_37, negated_conjecture, ~(k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(assume_negation,[status(cth)],[t66_relat_1])).
% 0.20/0.40  cnf(c_0_38, plain, (X1=k1_xboole_0|r2_hidden(k4_tarski(esk1_2(X1,k1_xboole_0),esk2_2(X1,k1_xboole_0)),X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_22]), c_0_36])).
% 0.20/0.40  fof(c_0_39, negated_conjecture, k4_relat_1(k1_xboole_0)!=k1_xboole_0, inference(fof_simplification,[status(thm)],[c_0_37])).
% 0.20/0.40  cnf(c_0_40, plain, (r2_hidden(k4_tarski(X2,X1),X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X3!=k4_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_41, plain, (k4_relat_1(X1)=k1_xboole_0|r2_hidden(k4_tarski(esk1_2(k4_relat_1(X1),k1_xboole_0),esk2_2(k4_relat_1(X1),k1_xboole_0)),k4_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_13])).
% 0.20/0.40  cnf(c_0_42, negated_conjecture, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_43, plain, (X1=X2|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.40  cnf(c_0_44, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X2,X1),k4_relat_1(X3))|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]), c_0_13])).
% 0.20/0.40  cnf(c_0_45, plain, (r2_hidden(k4_tarski(esk1_2(k4_relat_1(k1_xboole_0),k1_xboole_0),esk2_2(k4_relat_1(k1_xboole_0),k1_xboole_0)),k4_relat_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_22]), c_0_42])).
% 0.20/0.40  cnf(c_0_46, plain, (X1=k4_relat_1(X2)|~r2_hidden(k4_tarski(esk1_2(X1,k4_relat_1(X2)),esk2_2(X1,k4_relat_1(X2))),X1)|~r2_hidden(k4_tarski(esk2_2(X1,k4_relat_1(X2)),esk1_2(X1,k4_relat_1(X2))),X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_20]), c_0_13])).
% 0.20/0.40  cnf(c_0_47, plain, (r2_hidden(k4_tarski(esk2_2(k4_relat_1(k1_xboole_0),k1_xboole_0),esk1_2(k4_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_22])])).
% 0.20/0.40  cnf(c_0_48, plain, (X1=X2|~r2_hidden(k4_tarski(esk2_2(X1,X2),esk1_2(X1,X2)),k4_relat_1(X2))|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_33]), c_0_13])).
% 0.20/0.40  cnf(c_0_49, plain, (r2_hidden(k4_tarski(esk2_2(k4_relat_1(k1_xboole_0),k1_xboole_0),esk1_2(k4_relat_1(k1_xboole_0),k1_xboole_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_47]), c_0_22]), c_0_34])])).
% 0.20/0.40  cnf(c_0_50, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_45]), c_0_22])]), c_0_42])).
% 0.20/0.40  cnf(c_0_51, plain, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_13]), c_0_22])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 52
% 0.20/0.40  # Proof object clause steps            : 34
% 0.20/0.40  # Proof object formula steps           : 18
% 0.20/0.40  # Proof object conjectures             : 4
% 0.20/0.40  # Proof object clause conjectures      : 1
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 13
% 0.20/0.40  # Proof object initial formulas used   : 9
% 0.20/0.40  # Proof object generating inferences   : 19
% 0.20/0.40  # Proof object simplifying inferences  : 26
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 9
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 17
% 0.20/0.40  # Removed in clause preprocessing      : 2
% 0.20/0.40  # Initial clauses in saturation        : 15
% 0.20/0.40  # Processed clauses                    : 110
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 33
% 0.20/0.40  # ...remaining for further processing  : 77
% 0.20/0.40  # Other redundant clauses eliminated   : 2
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 16
% 0.20/0.40  # Backward-rewritten                   : 1
% 0.20/0.40  # Generated clauses                    : 144
% 0.20/0.40  # ...of the previous two non-trivial   : 121
% 0.20/0.40  # Contextual simplify-reflections      : 11
% 0.20/0.40  # Paramodulations                      : 142
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 2
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 43
% 0.20/0.40  #    Positive orientable unit clauses  : 5
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 2
% 0.20/0.40  #    Non-unit-clauses                  : 36
% 0.20/0.40  # Current number of unprocessed clauses: 31
% 0.20/0.40  # ...number of literals in the above   : 116
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 32
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 965
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 428
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 60
% 0.20/0.40  # Unit Clause-clause subsumption calls : 12
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 3
% 0.20/0.40  # BW rewrite match successes           : 1
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 4798
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.051 s
% 0.20/0.41  # System time              : 0.007 s
% 0.20/0.41  # Total time               : 0.058 s
% 0.20/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
