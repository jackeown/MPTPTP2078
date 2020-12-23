%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t42_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:13 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  76 expanded)
%              Number of clauses        :   20 (  27 expanded)
%              Number of leaves         :    5 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  173 ( 509 expanded)
%              Number of equality atoms :   26 (  62 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3))
          & ! [X4] :
              ( r2_hidden(X4,k1_wellord1(X3,X1))
             => ( r2_hidden(k4_tarski(X4,X2),X3)
                & X4 != X2 ) ) )
       => r2_hidden(k4_tarski(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t42_wellord1.p',t42_wellord1)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t42_wellord1.p',d4_wellord1)).

fof(l4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
      <=> ! [X2,X3] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r2_hidden(X3,k3_relat_1(X1))
              & X2 != X3
              & ~ r2_hidden(k4_tarski(X2,X3),X1)
              & ~ r2_hidden(k4_tarski(X3,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t42_wellord1.p',l4_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t42_wellord1.p',d1_wellord1)).

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t42_wellord1.p',l1_wellord1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( ( v2_wellord1(X3)
            & r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3))
            & ! [X4] :
                ( r2_hidden(X4,k1_wellord1(X3,X1))
               => ( r2_hidden(k4_tarski(X4,X2),X3)
                  & X4 != X2 ) ) )
         => r2_hidden(k4_tarski(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t42_wellord1])).

fof(c_0_6,plain,(
    ! [X21] :
      ( ( v1_relat_2(X21)
        | ~ v2_wellord1(X21)
        | ~ v1_relat_1(X21) )
      & ( v8_relat_2(X21)
        | ~ v2_wellord1(X21)
        | ~ v1_relat_1(X21) )
      & ( v4_relat_2(X21)
        | ~ v2_wellord1(X21)
        | ~ v1_relat_1(X21) )
      & ( v6_relat_2(X21)
        | ~ v2_wellord1(X21)
        | ~ v1_relat_1(X21) )
      & ( v1_wellord1(X21)
        | ~ v2_wellord1(X21)
        | ~ v1_relat_1(X21) )
      & ( ~ v1_relat_2(X21)
        | ~ v8_relat_2(X21)
        | ~ v4_relat_2(X21)
        | ~ v6_relat_2(X21)
        | ~ v1_wellord1(X21)
        | v2_wellord1(X21)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_7,negated_conjecture,(
    ! [X8] :
      ( v1_relat_1(esk3_0)
      & v2_wellord1(esk3_0)
      & r2_hidden(esk1_0,k3_relat_1(esk3_0))
      & r2_hidden(esk2_0,k3_relat_1(esk3_0))
      & ( r2_hidden(k4_tarski(X8,esk2_0),esk3_0)
        | ~ r2_hidden(X8,k1_wellord1(esk3_0,esk1_0)) )
      & ( X8 != esk2_0
        | ~ r2_hidden(X8,k1_wellord1(esk3_0,esk1_0)) )
      & ~ r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).

fof(c_0_8,plain,(
    ! [X28,X29,X30] :
      ( ( ~ v6_relat_2(X28)
        | ~ r2_hidden(X29,k3_relat_1(X28))
        | ~ r2_hidden(X30,k3_relat_1(X28))
        | X29 = X30
        | r2_hidden(k4_tarski(X29,X30),X28)
        | r2_hidden(k4_tarski(X30,X29),X28)
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(esk7_1(X28),k3_relat_1(X28))
        | v6_relat_2(X28)
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(esk8_1(X28),k3_relat_1(X28))
        | v6_relat_2(X28)
        | ~ v1_relat_1(X28) )
      & ( esk7_1(X28) != esk8_1(X28)
        | v6_relat_2(X28)
        | ~ v1_relat_1(X28) )
      & ( ~ r2_hidden(k4_tarski(esk7_1(X28),esk8_1(X28)),X28)
        | v6_relat_2(X28)
        | ~ v1_relat_1(X28) )
      & ( ~ r2_hidden(k4_tarski(esk8_1(X28),esk7_1(X28)),X28)
        | v6_relat_2(X28)
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

cnf(c_0_9,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v2_wellord1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19] :
      ( ( X16 != X14
        | ~ r2_hidden(X16,X15)
        | X15 != k1_wellord1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(X16,X14),X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k1_wellord1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( X17 = X14
        | ~ r2_hidden(k4_tarski(X17,X14),X13)
        | r2_hidden(X17,X15)
        | X15 != k1_wellord1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(esk4_3(X13,X18,X19),X19)
        | esk4_3(X13,X18,X19) = X18
        | ~ r2_hidden(k4_tarski(esk4_3(X13,X18,X19),X18),X13)
        | X19 = k1_wellord1(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( esk4_3(X13,X18,X19) != X18
        | r2_hidden(esk4_3(X13,X18,X19),X19)
        | X19 = k1_wellord1(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk4_3(X13,X18,X19),X18),X13)
        | r2_hidden(esk4_3(X13,X18,X19),X19)
        | X19 = k1_wellord1(X13,X18)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_13,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk2_0,k3_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( v6_relat_2(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_16,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( X1 = esk2_0
    | r2_hidden(k4_tarski(X1,esk2_0),esk3_0)
    | r2_hidden(k4_tarski(esk2_0,X1),esk3_0)
    | ~ r2_hidden(X1,k3_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_11])])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk1_0,k3_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( X1 != esk2_0
    | ~ r2_hidden(X1,k1_wellord1(esk3_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_21,plain,(
    ! [X25,X26] :
      ( ( ~ v1_relat_2(X25)
        | ~ r2_hidden(X26,k3_relat_1(X25))
        | r2_hidden(k4_tarski(X26,X26),X25)
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(esk6_1(X25),k3_relat_1(X25))
        | v1_relat_2(X25)
        | ~ v1_relat_1(X25) )
      & ( ~ r2_hidden(k4_tarski(esk6_1(X25),esk6_1(X25)),X25)
        | v1_relat_2(X25)
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).

cnf(c_0_22,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( esk2_0 = esk1_0
    | r2_hidden(k4_tarski(esk2_0,esk1_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_wellord1(esk3_0,esk1_0)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X2,X2),X1)
    | ~ v1_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_2(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_10]),c_0_11])])).

cnf(c_0_28,negated_conjecture,
    ( esk2_0 = esk1_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_11])]),c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk1_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_18]),c_0_27]),c_0_11])])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_28]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
