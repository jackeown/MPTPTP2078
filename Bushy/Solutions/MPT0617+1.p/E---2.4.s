%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t9_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:28 EDT 2019

% Result     : Theorem 96.38s
% Output     : CNFRefutation 96.38s
% Verified   : 
% Statistics : Number of formulae       :   42 (1198 expanded)
%              Number of clauses        :   33 ( 469 expanded)
%              Number of leaves         :    4 ( 279 expanded)
%              Depth                    :   15
%              Number of atoms          :  174 (7516 expanded)
%              Number of equality atoms :   48 (2456 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t9_funct_1.p',d4_relat_1)).

fof(t9_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t9_funct_1.p',t9_funct_1)).

fof(d2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X1 = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X1)
              <=> r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t9_funct_1.p',d2_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/funct_1__t9_funct_1.p',d4_funct_1)).

fof(c_0_4,plain,(
    ! [X21,X22,X23,X25,X26,X27,X28,X30] :
      ( ( ~ r2_hidden(X23,X22)
        | r2_hidden(k4_tarski(X23,esk5_3(X21,X22,X23)),X21)
        | X22 != k1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(X25,X26),X21)
        | r2_hidden(X25,X22)
        | X22 != k1_relat_1(X21) )
      & ( ~ r2_hidden(esk6_2(X27,X28),X28)
        | ~ r2_hidden(k4_tarski(esk6_2(X27,X28),X30),X27)
        | X28 = k1_relat_1(X27) )
      & ( r2_hidden(esk6_2(X27,X28),X28)
        | r2_hidden(k4_tarski(esk6_2(X27,X28),esk7_2(X27,X28)),X27)
        | X28 = k1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( k1_relat_1(X1) = k1_relat_1(X2)
                & ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                   => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_funct_1])).

cnf(c_0_6,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_7,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(k4_tarski(X12,X13),X10)
        | r2_hidden(k4_tarski(X12,X13),X11)
        | X10 != X11
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(k4_tarski(X14,X15),X11)
        | r2_hidden(k4_tarski(X14,X15),X10)
        | X10 != X11
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X10,X11),esk4_2(X10,X11)),X10)
        | ~ r2_hidden(k4_tarski(esk3_2(X10,X11),esk4_2(X10,X11)),X11)
        | X10 = X11
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(esk3_2(X10,X11),esk4_2(X10,X11)),X10)
        | r2_hidden(k4_tarski(esk3_2(X10,X11),esk4_2(X10,X11)),X11)
        | X10 = X11
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_relat_1])])])])])])).

fof(c_0_8,plain,(
    ! [X18,X19,X20] :
      ( ( X20 != k1_funct_1(X18,X19)
        | r2_hidden(k4_tarski(X19,X20),X18)
        | ~ r2_hidden(X19,k1_relat_1(X18))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X19,X20),X18)
        | X20 = k1_funct_1(X18,X19)
        | ~ r2_hidden(X19,k1_relat_1(X18))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( X20 != k1_funct_1(X18,X19)
        | X20 = k1_xboole_0
        | r2_hidden(X19,k1_relat_1(X18))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( X20 != k1_xboole_0
        | X20 = k1_funct_1(X18,X19)
        | r2_hidden(X19,k1_relat_1(X18))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_9,negated_conjecture,(
    ! [X7] :
      ( v1_relat_1(esk1_0)
      & v1_funct_1(esk1_0)
      & v1_relat_1(esk2_0)
      & v1_funct_1(esk2_0)
      & k1_relat_1(esk1_0) = k1_relat_1(esk2_0)
      & ( ~ r2_hidden(X7,k1_relat_1(esk1_0))
        | k1_funct_1(esk1_0,X7) = k1_funct_1(esk2_0,X7) )
      & esk1_0 != esk2_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)
    | X1 = X2
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( X2 = k1_funct_1(X3,X1)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( k1_relat_1(esk1_0) = k1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( X1 = X2
    | r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)
    | r2_hidden(esk3_2(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( X1 = k1_funct_1(esk2_0,X2)
    | ~ r2_hidden(k4_tarski(X2,X1),esk2_0)
    | ~ r2_hidden(X2,k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_20,plain,
    ( X1 = X2
    | r2_hidden(esk3_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk3_2(X1,X2),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk2_0,X1)),esk2_0)
    | ~ r2_hidden(X1,k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_23,negated_conjecture,
    ( X1 = k1_funct_1(esk2_0,esk3_2(X2,esk1_0))
    | X2 = esk1_0
    | r2_hidden(esk3_2(X2,esk1_0),k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(esk3_2(X2,esk1_0),X1),esk2_0)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_24,plain,
    ( X1 = X2
    | r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | r2_hidden(esk3_2(X1,X2),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( X1 = esk1_0
    | r2_hidden(k4_tarski(esk3_2(X1,esk1_0),k1_funct_1(esk2_0,esk3_2(X1,esk1_0))),esk2_0)
    | r2_hidden(esk3_2(X1,esk1_0),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_21])])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(esk2_0,esk3_2(esk2_0,esk1_0)) = esk4_2(esk2_0,esk1_0)
    | r2_hidden(esk3_2(esk2_0,esk1_0),k1_relat_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_14]),c_0_16]),c_0_21])]),c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(esk2_0,esk1_0),esk4_2(esk2_0,esk1_0)),esk2_0)
    | r2_hidden(esk3_2(esk2_0,esk1_0),k1_relat_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_14]),c_0_16])]),c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( k1_funct_1(esk1_0,X1) = k1_funct_1(esk2_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk3_2(esk2_0,esk1_0),k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_28]),c_0_14])])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(esk2_0,esk3_2(esk2_0,esk1_0)) = k1_funct_1(esk1_0,esk3_2(esk2_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k1_funct_1(esk1_0,esk3_2(esk2_0,esk1_0))
    | ~ r2_hidden(k4_tarski(esk3_2(esk2_0,esk1_0),X1),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_30]),c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( X1 = k1_funct_1(esk1_0,esk3_2(esk2_0,esk1_0))
    | ~ r2_hidden(k4_tarski(esk3_2(esk2_0,esk1_0),X1),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_30]),c_0_32]),c_0_21])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(esk2_0,esk1_0),k1_funct_1(esk1_0,esk3_2(esk2_0,esk1_0))),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_30]),c_0_32]),c_0_21])])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(esk1_0,esk3_2(esk2_0,esk1_0)) = esk4_2(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_11]),c_0_21]),c_0_16])]),c_0_25]),c_0_34])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(esk2_0,esk1_0),esk4_2(esk2_0,esk1_0)),esk1_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(esk2_0,esk1_0),k1_funct_1(esk1_0,esk3_2(esk2_0,esk1_0))),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_30]),c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk3_2(esk2_0,esk1_0),esk4_2(esk2_0,esk1_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_21]),c_0_16])]),c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_36]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
