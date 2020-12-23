%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0792+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:12 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   31 (  76 expanded)
%              Number of clauses        :   20 (  27 expanded)
%              Number of leaves         :    5 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :  177 ( 513 expanded)
%              Number of equality atoms :   27 (  63 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_wellord1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

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
    ! [X17,X18,X19] :
      ( ( ~ v6_relat_2(X17)
        | ~ r2_hidden(X18,k3_relat_1(X17))
        | ~ r2_hidden(X19,k3_relat_1(X17))
        | X18 = X19
        | r2_hidden(k4_tarski(X18,X19),X17)
        | r2_hidden(k4_tarski(X19,X18),X17)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(esk3_1(X17),k3_relat_1(X17))
        | v6_relat_2(X17)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(esk4_1(X17),k3_relat_1(X17))
        | v6_relat_2(X17)
        | ~ v1_relat_1(X17) )
      & ( esk3_1(X17) != esk4_1(X17)
        | v6_relat_2(X17)
        | ~ v1_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(esk3_1(X17),esk4_1(X17)),X17)
        | v6_relat_2(X17)
        | ~ v1_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(esk4_1(X17),esk3_1(X17)),X17)
        | v6_relat_2(X17)
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

fof(c_0_7,negated_conjecture,(
    ! [X25] :
      ( v1_relat_1(esk7_0)
      & v2_wellord1(esk7_0)
      & r2_hidden(esk5_0,k3_relat_1(esk7_0))
      & r2_hidden(esk6_0,k3_relat_1(esk7_0))
      & ( r2_hidden(k4_tarski(X25,esk6_0),esk7_0)
        | ~ r2_hidden(X25,k1_wellord1(esk7_0,esk5_0)) )
      & ( X25 != esk6_0
        | ~ r2_hidden(X25,k1_wellord1(esk7_0,esk5_0)) )
      & ~ r2_hidden(k4_tarski(esk5_0,esk6_0),esk7_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).

cnf(c_0_8,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk6_0,k3_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X13] :
      ( ( v1_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v8_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v4_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v6_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v1_wellord1(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( ~ v1_relat_2(X13)
        | ~ v8_relat_2(X13)
        | ~ v4_relat_2(X13)
        | ~ v6_relat_2(X13)
        | ~ v1_wellord1(X13)
        | v2_wellord1(X13)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_12,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11] :
      ( ( X8 != X6
        | ~ r2_hidden(X8,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(X8,X6),X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( X9 = X6
        | ~ r2_hidden(k4_tarski(X9,X6),X5)
        | r2_hidden(X9,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(esk1_3(X5,X10,X11),X11)
        | esk1_3(X5,X10,X11) = X10
        | ~ r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) )
      & ( esk1_3(X5,X10,X11) != X10
        | r2_hidden(esk1_3(X5,X10,X11),X11)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5)
        | r2_hidden(esk1_3(X5,X10,X11),X11)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_13,negated_conjecture,
    ( X1 = esk6_0
    | r2_hidden(k4_tarski(esk6_0,X1),esk7_0)
    | r2_hidden(k4_tarski(X1,esk6_0),esk7_0)
    | ~ v6_relat_2(esk7_0)
    | ~ r2_hidden(X1,k3_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_14,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v2_wellord1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( X1 = esk6_0
    | r2_hidden(k4_tarski(X1,esk6_0),esk7_0)
    | r2_hidden(k4_tarski(esk6_0,X1),esk7_0)
    | ~ r2_hidden(X1,k3_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_10])])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk5_0,k3_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk5_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( X1 != esk6_0
    | ~ r2_hidden(X1,k1_wellord1(esk7_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( esk6_0 = esk5_0
    | r2_hidden(k4_tarski(esk6_0,esk5_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k1_wellord1(esk7_0,esk5_0)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( esk6_0 = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_10])]),c_0_23])).

fof(c_0_25,plain,(
    ! [X14,X15] :
      ( ( ~ v1_relat_2(X14)
        | ~ r2_hidden(X15,k3_relat_1(X14))
        | r2_hidden(k4_tarski(X15,X15),X14)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk2_1(X14),k3_relat_1(X14))
        | v1_relat_2(X14)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(esk2_1(X14),esk2_1(X14)),X14)
        | v1_relat_2(X14)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk5_0,esk5_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_24])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X2,X2),X1)
    | ~ v1_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_relat_2(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_18]),c_0_10])])).

cnf(c_0_29,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_15]),c_0_10])]),
    [proof]).

%------------------------------------------------------------------------------
