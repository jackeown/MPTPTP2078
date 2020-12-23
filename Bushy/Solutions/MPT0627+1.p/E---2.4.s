%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t22_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:22 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 152 expanded)
%              Number of clauses        :   25 (  55 expanded)
%              Number of leaves         :    6 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  195 ( 829 expanded)
%              Number of equality atoms :   32 ( 141 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t22_funct_1.p',d4_funct_1)).

fof(t22_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
           => k1_funct_1(k5_relat_1(X3,X2),X1) = k1_funct_1(X2,k1_funct_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t22_funct_1.p',t22_funct_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t22_funct_1.p',fc2_funct_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t22_funct_1.p',d4_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/funct_1__t22_funct_1.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t22_funct_1.p',dt_k5_relat_1)).

fof(c_0_6,plain,(
    ! [X12,X13,X14] :
      ( ( X14 != k1_funct_1(X12,X13)
        | r2_hidden(k4_tarski(X13,X14),X12)
        | ~ r2_hidden(X13,k1_relat_1(X12))
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X14 = k1_funct_1(X12,X13)
        | ~ r2_hidden(X13,k1_relat_1(X12))
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( X14 != k1_funct_1(X12,X13)
        | X14 = k1_xboole_0
        | r2_hidden(X13,k1_relat_1(X12))
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( X14 != k1_xboole_0
        | X14 = k1_funct_1(X12,X13)
        | r2_hidden(X13,k1_relat_1(X12))
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
             => k1_funct_1(k5_relat_1(X3,X2),X1) = k1_funct_1(X2,k1_funct_1(X3,X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t22_funct_1])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,esk2_0)))
    & k1_funct_1(k5_relat_1(esk3_0,esk2_0),esk1_0) != k1_funct_1(esk2_0,k1_funct_1(esk3_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(k5_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X52,X53] :
      ( ( v1_relat_1(k5_relat_1(X52,X53))
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52)
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) )
      & ( v1_funct_1(k5_relat_1(X52,X53))
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52)
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

fof(c_0_13,plain,(
    ! [X15,X16,X17,X19,X20,X21,X22,X24] :
      ( ( ~ r2_hidden(X17,X16)
        | r2_hidden(k4_tarski(X17,esk4_3(X15,X16,X17)),X15)
        | X16 != k1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X19,X20),X15)
        | r2_hidden(X19,X16)
        | X16 != k1_relat_1(X15) )
      & ( ~ r2_hidden(esk5_2(X21,X22),X22)
        | ~ r2_hidden(k4_tarski(esk5_2(X21,X22),X24),X21)
        | X22 = k1_relat_1(X21) )
      & ( r2_hidden(esk5_2(X21,X22),X22)
        | r2_hidden(k4_tarski(esk5_2(X21,X22),esk6_2(X21,X22)),X21)
        | X22 = k1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_14,plain,(
    ! [X26,X27,X28,X29,X30,X32,X33,X34,X37] :
      ( ( r2_hidden(k4_tarski(X29,esk7_5(X26,X27,X28,X29,X30)),X26)
        | ~ r2_hidden(k4_tarski(X29,X30),X28)
        | X28 != k5_relat_1(X26,X27)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27)
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(k4_tarski(esk7_5(X26,X27,X28,X29,X30),X30),X27)
        | ~ r2_hidden(k4_tarski(X29,X30),X28)
        | X28 != k5_relat_1(X26,X27)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27)
        | ~ v1_relat_1(X26) )
      & ( ~ r2_hidden(k4_tarski(X32,X34),X26)
        | ~ r2_hidden(k4_tarski(X34,X33),X27)
        | r2_hidden(k4_tarski(X32,X33),X28)
        | X28 != k5_relat_1(X26,X27)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27)
        | ~ v1_relat_1(X26) )
      & ( ~ r2_hidden(k4_tarski(esk8_3(X26,X27,X28),esk9_3(X26,X27,X28)),X28)
        | ~ r2_hidden(k4_tarski(esk8_3(X26,X27,X28),X37),X26)
        | ~ r2_hidden(k4_tarski(X37,esk9_3(X26,X27,X28)),X27)
        | X28 = k5_relat_1(X26,X27)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27)
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(k4_tarski(esk8_3(X26,X27,X28),esk10_3(X26,X27,X28)),X26)
        | r2_hidden(k4_tarski(esk8_3(X26,X27,X28),esk9_3(X26,X27,X28)),X28)
        | X28 = k5_relat_1(X26,X27)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27)
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(k4_tarski(esk10_3(X26,X27,X28),esk9_3(X26,X27,X28)),X27)
        | r2_hidden(k4_tarski(esk8_3(X26,X27,X28),esk9_3(X26,X27,X28)),X28)
        | X28 = k5_relat_1(X26,X27)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_15,plain,(
    ! [X39,X40] :
      ( ~ v1_relat_1(X39)
      | ~ v1_relat_1(X40)
      | v1_relat_1(k5_relat_1(X39,X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,k1_funct_1(k5_relat_1(esk3_0,esk2_0),esk1_0)),k5_relat_1(esk3_0,esk2_0))
    | ~ v1_funct_1(k5_relat_1(esk3_0,esk2_0))
    | ~ v1_relat_1(k5_relat_1(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,esk7_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,k1_funct_1(k5_relat_1(esk3_0,esk2_0),esk1_0)),k5_relat_1(esk3_0,esk2_0))
    | ~ v1_relat_1(k5_relat_1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_26,plain,
    ( X2 = k1_funct_1(X3,X1)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X1,esk7_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,k1_funct_1(k5_relat_1(esk3_0,esk2_0),esk1_0)),k5_relat_1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_20]),c_0_21])])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(esk7_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk7_5(esk3_0,esk2_0,k5_relat_1(esk3_0,esk2_0),esk1_0,k1_funct_1(k5_relat_1(esk3_0,esk2_0),esk1_0))),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_20]),c_0_21])])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(esk7_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]),c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( esk7_5(esk3_0,esk2_0,k5_relat_1(esk3_0,esk2_0),esk1_0,k1_funct_1(k5_relat_1(esk3_0,esk2_0),esk1_0)) = k1_funct_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_19]),c_0_21])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(esk3_0,esk1_0),k1_funct_1(k5_relat_1(esk3_0,esk2_0),esk1_0)),esk2_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_29]),c_0_20]),c_0_21])]),c_0_34])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk3_0,esk2_0),esk1_0) != k1_funct_1(esk2_0,k1_funct_1(esk3_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_35]),c_0_18]),c_0_20])]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
