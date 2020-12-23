%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:56 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 426 expanded)
%              Number of clauses        :   41 ( 173 expanded)
%              Number of leaves         :    8 (  99 expanded)
%              Depth                    :   19
%              Number of atoms          :  318 (2706 expanded)
%              Number of equality atoms :   49 ( 374 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   51 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) )
       => ( r2_hidden(k4_tarski(X1,X2),X3)
        <=> r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t36_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( ( v2_wellord1(X2)
          & r1_tarski(X1,k3_relat_1(X2)) )
       => ( ~ ( X1 != k3_relat_1(X2)
              & ! [X3] :
                  ~ ( r2_hidden(X3,k3_relat_1(X2))
                    & X1 = k1_wellord1(X2,X3) ) )
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
             => ! [X4] :
                  ( r2_hidden(k4_tarski(X4,X3),X2)
                 => r2_hidden(X4,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_wellord1)).

fof(t13_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_wellord1(X2,X1),k3_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_wellord1)).

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( ( v2_wellord1(X3)
            & r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3)) )
         => ( r2_hidden(k4_tarski(X1,X2),X3)
          <=> r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_wellord1])).

fof(c_0_9,plain,(
    ! [X23,X24,X25] :
      ( ( ~ v6_relat_2(X23)
        | ~ r2_hidden(X24,k3_relat_1(X23))
        | ~ r2_hidden(X25,k3_relat_1(X23))
        | X24 = X25
        | r2_hidden(k4_tarski(X24,X25),X23)
        | r2_hidden(k4_tarski(X25,X24),X23)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(esk4_1(X23),k3_relat_1(X23))
        | v6_relat_2(X23)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(esk5_1(X23),k3_relat_1(X23))
        | v6_relat_2(X23)
        | ~ v1_relat_1(X23) )
      & ( esk4_1(X23) != esk5_1(X23)
        | v6_relat_2(X23)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(esk4_1(X23),esk5_1(X23)),X23)
        | v6_relat_2(X23)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(esk5_1(X23),esk4_1(X23)),X23)
        | v6_relat_2(X23)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk11_0)
    & v2_wellord1(esk11_0)
    & r2_hidden(esk9_0,k3_relat_1(esk11_0))
    & r2_hidden(esk10_0,k3_relat_1(esk11_0))
    & ( ~ r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)
      | ~ r1_tarski(k1_wellord1(esk11_0,esk9_0),k1_wellord1(esk11_0,esk10_0)) )
    & ( r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)
      | r1_tarski(k1_wellord1(esk11_0,esk9_0),k1_wellord1(esk11_0,esk10_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_11,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk10_0,k3_relat_1(esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X19] :
      ( ( v1_relat_2(X19)
        | ~ v2_wellord1(X19)
        | ~ v1_relat_1(X19) )
      & ( v8_relat_2(X19)
        | ~ v2_wellord1(X19)
        | ~ v1_relat_1(X19) )
      & ( v4_relat_2(X19)
        | ~ v2_wellord1(X19)
        | ~ v1_relat_1(X19) )
      & ( v6_relat_2(X19)
        | ~ v2_wellord1(X19)
        | ~ v1_relat_1(X19) )
      & ( v1_wellord1(X19)
        | ~ v2_wellord1(X19)
        | ~ v1_relat_1(X19) )
      & ( ~ v1_relat_2(X19)
        | ~ v8_relat_2(X19)
        | ~ v4_relat_2(X19)
        | ~ v6_relat_2(X19)
        | ~ v1_wellord1(X19)
        | v2_wellord1(X19)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_15,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17] :
      ( ( X14 != X12
        | ~ r2_hidden(X14,X13)
        | X13 != k1_wellord1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(X14,X12),X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k1_wellord1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( X15 = X12
        | ~ r2_hidden(k4_tarski(X15,X12),X11)
        | r2_hidden(X15,X13)
        | X13 != k1_wellord1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(esk2_3(X11,X16,X17),X17)
        | esk2_3(X11,X16,X17) = X16
        | ~ r2_hidden(k4_tarski(esk2_3(X11,X16,X17),X16),X11)
        | X17 = k1_wellord1(X11,X16)
        | ~ v1_relat_1(X11) )
      & ( esk2_3(X11,X16,X17) != X16
        | r2_hidden(esk2_3(X11,X16,X17),X17)
        | X17 = k1_wellord1(X11,X16)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk2_3(X11,X16,X17),X16),X11)
        | r2_hidden(esk2_3(X11,X16,X17),X17)
        | X17 = k1_wellord1(X11,X16)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_16,negated_conjecture,
    ( X1 = esk10_0
    | r2_hidden(k4_tarski(esk10_0,X1),esk11_0)
    | r2_hidden(k4_tarski(X1,esk10_0),esk11_0)
    | ~ v6_relat_2(esk11_0)
    | ~ r2_hidden(X1,k3_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_17,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v2_wellord1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( X1 = esk10_0
    | r2_hidden(k4_tarski(X1,esk10_0),esk11_0)
    | r2_hidden(k4_tarski(esk10_0,X1),esk11_0)
    | ~ r2_hidden(X1,k3_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_13])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk9_0,k3_relat_1(esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_22,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_23,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( esk10_0 = esk9_0
    | r2_hidden(k4_tarski(esk10_0,esk9_0),esk11_0)
    | r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)
    | r1_tarski(k1_wellord1(esk11_0,esk9_0),k1_wellord1(esk11_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( esk10_0 = esk9_0
    | r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)
    | r2_hidden(esk10_0,k1_wellord1(esk11_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_13])])).

fof(c_0_28,plain,(
    ! [X30,X31,X32,X33,X34] :
      ( ( X30 != k3_relat_1(X31)
        | ~ r2_hidden(X33,X30)
        | ~ r2_hidden(k4_tarski(X34,X33),X31)
        | r2_hidden(X34,X30)
        | ~ v2_wellord1(X31)
        | ~ r1_tarski(X30,k3_relat_1(X31))
        | ~ v1_relat_1(X31) )
      & ( ~ r2_hidden(X32,k3_relat_1(X31))
        | X30 != k1_wellord1(X31,X32)
        | ~ r2_hidden(X33,X30)
        | ~ r2_hidden(k4_tarski(X34,X33),X31)
        | r2_hidden(X34,X30)
        | ~ v2_wellord1(X31)
        | ~ r1_tarski(X30,k3_relat_1(X31))
        | ~ v1_relat_1(X31) )
      & ( r2_hidden(esk8_2(X30,X31),k3_relat_1(X31))
        | X30 = k3_relat_1(X31)
        | r2_hidden(esk6_2(X30,X31),X30)
        | ~ v2_wellord1(X31)
        | ~ r1_tarski(X30,k3_relat_1(X31))
        | ~ v1_relat_1(X31) )
      & ( X30 = k1_wellord1(X31,esk8_2(X30,X31))
        | X30 = k3_relat_1(X31)
        | r2_hidden(esk6_2(X30,X31),X30)
        | ~ v2_wellord1(X31)
        | ~ r1_tarski(X30,k3_relat_1(X31))
        | ~ v1_relat_1(X31) )
      & ( r2_hidden(esk8_2(X30,X31),k3_relat_1(X31))
        | X30 = k3_relat_1(X31)
        | r2_hidden(k4_tarski(esk7_2(X30,X31),esk6_2(X30,X31)),X31)
        | ~ v2_wellord1(X31)
        | ~ r1_tarski(X30,k3_relat_1(X31))
        | ~ v1_relat_1(X31) )
      & ( X30 = k1_wellord1(X31,esk8_2(X30,X31))
        | X30 = k3_relat_1(X31)
        | r2_hidden(k4_tarski(esk7_2(X30,X31),esk6_2(X30,X31)),X31)
        | ~ v2_wellord1(X31)
        | ~ r1_tarski(X30,k3_relat_1(X31))
        | ~ v1_relat_1(X31) )
      & ( r2_hidden(esk8_2(X30,X31),k3_relat_1(X31))
        | X30 = k3_relat_1(X31)
        | ~ r2_hidden(esk7_2(X30,X31),X30)
        | ~ v2_wellord1(X31)
        | ~ r1_tarski(X30,k3_relat_1(X31))
        | ~ v1_relat_1(X31) )
      & ( X30 = k1_wellord1(X31,esk8_2(X30,X31))
        | X30 = k3_relat_1(X31)
        | ~ r2_hidden(esk7_2(X30,X31),X30)
        | ~ v2_wellord1(X31)
        | ~ r1_tarski(X30,k3_relat_1(X31))
        | ~ v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_wellord1])])])])])).

fof(c_0_29,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | r1_tarski(k1_wellord1(X29,X28),k3_relat_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_wellord1])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)
    | r2_hidden(X1,k1_wellord1(esk11_0,esk10_0))
    | ~ r2_hidden(X1,k1_wellord1(esk11_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( esk10_0 = esk9_0
    | r2_hidden(esk10_0,k1_wellord1(esk11_0,esk9_0))
    | r2_hidden(esk9_0,k1_wellord1(esk11_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_27]),c_0_13])])).

cnf(c_0_32,plain,
    ( r2_hidden(X5,X3)
    | ~ r2_hidden(X1,k3_relat_1(X2))
    | X3 != k1_wellord1(X2,X1)
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(k4_tarski(X5,X4),X2)
    | ~ v2_wellord1(X2)
    | ~ r1_tarski(X3,k3_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,X3)
    | X3 != k1_wellord1(X4,X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( esk10_0 = esk9_0
    | r2_hidden(esk9_0,k1_wellord1(esk11_0,esk10_0))
    | r2_hidden(esk10_0,k1_wellord1(esk11_0,esk10_0))
    | r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k1_wellord1(X2,X3))
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,k1_wellord1(X2,X3))
    | ~ r2_hidden(X3,k3_relat_1(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_33])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_wellord1(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).

cnf(c_0_40,negated_conjecture,
    ( esk10_0 = esk9_0
    | r2_hidden(esk10_0,k1_wellord1(esk11_0,esk10_0))
    | r2_hidden(esk9_0,k1_wellord1(esk11_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_36]),c_0_13])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k1_wellord1(X2,X3))
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X4,k1_wellord1(X2,X3))
    | ~ r2_hidden(X1,k1_wellord1(X2,X4))
    | ~ r2_hidden(X3,k3_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( esk10_0 = esk9_0
    | r2_hidden(esk9_0,k1_wellord1(esk11_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_13])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_44,negated_conjecture,
    ( esk10_0 = esk9_0
    | r2_hidden(X1,k1_wellord1(esk11_0,esk10_0))
    | ~ r2_hidden(X1,k1_wellord1(esk11_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_18]),c_0_13]),c_0_12])])).

cnf(c_0_45,negated_conjecture,
    ( esk10_0 = esk9_0
    | r1_tarski(X1,k1_wellord1(esk11_0,esk10_0))
    | ~ r2_hidden(esk1_2(X1,k1_wellord1(esk11_0,esk10_0)),k1_wellord1(esk11_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_46,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)
    | ~ r1_tarski(k1_wellord1(esk11_0,esk9_0),k1_wellord1(esk11_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_48,negated_conjecture,
    ( esk10_0 = esk9_0
    | r1_tarski(k1_wellord1(esk11_0,esk9_0),k1_wellord1(esk11_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( esk10_0 = esk9_0
    | ~ r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_50,negated_conjecture,
    ( esk10_0 = esk9_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_38]),c_0_13])]),c_0_42])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_46])).

fof(c_0_52,plain,(
    ! [X20,X21] :
      ( ( ~ v1_relat_2(X20)
        | ~ r2_hidden(X21,k3_relat_1(X20))
        | r2_hidden(k4_tarski(X21,X21),X20)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(esk3_1(X20),k3_relat_1(X20))
        | v1_relat_2(X20)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(esk3_1(X20),esk3_1(X20)),X20)
        | v1_relat_2(X20)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk9_0,esk9_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_50]),c_0_50]),c_0_51])])).

cnf(c_0_54,plain,
    ( r2_hidden(k4_tarski(X2,X2),X1)
    | ~ v1_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_relat_2(esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_13]),c_0_21])])).

cnf(c_0_56,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_18]),c_0_13])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:49:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.52  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.19/0.52  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.52  #
% 0.19/0.52  # Preprocessing time       : 0.029 s
% 0.19/0.52  
% 0.19/0.52  # Proof found!
% 0.19/0.52  # SZS status Theorem
% 0.19/0.52  # SZS output start CNFRefutation
% 0.19/0.52  fof(t37_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_wellord1)).
% 0.19/0.52  fof(l4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v6_relat_2(X1)<=>![X2, X3]:~(((((r2_hidden(X2,k3_relat_1(X1))&r2_hidden(X3,k3_relat_1(X1)))&X2!=X3)&~(r2_hidden(k4_tarski(X2,X3),X1)))&~(r2_hidden(k4_tarski(X3,X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l4_wellord1)).
% 0.19/0.52  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 0.19/0.52  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 0.19/0.52  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.52  fof(t36_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>((v2_wellord1(X2)&r1_tarski(X1,k3_relat_1(X2)))=>(~((X1!=k3_relat_1(X2)&![X3]:~((r2_hidden(X3,k3_relat_1(X2))&X1=k1_wellord1(X2,X3)))))<=>![X3]:(r2_hidden(X3,X1)=>![X4]:(r2_hidden(k4_tarski(X4,X3),X2)=>r2_hidden(X4,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_wellord1)).
% 0.19/0.52  fof(t13_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_wellord1(X2,X1),k3_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_wellord1)).
% 0.19/0.52  fof(l1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v1_relat_2(X1)<=>![X2]:(r2_hidden(X2,k3_relat_1(X1))=>r2_hidden(k4_tarski(X2,X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_wellord1)).
% 0.19/0.52  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)))))), inference(assume_negation,[status(cth)],[t37_wellord1])).
% 0.19/0.52  fof(c_0_9, plain, ![X23, X24, X25]:((~v6_relat_2(X23)|(~r2_hidden(X24,k3_relat_1(X23))|~r2_hidden(X25,k3_relat_1(X23))|X24=X25|r2_hidden(k4_tarski(X24,X25),X23)|r2_hidden(k4_tarski(X25,X24),X23))|~v1_relat_1(X23))&(((((r2_hidden(esk4_1(X23),k3_relat_1(X23))|v6_relat_2(X23)|~v1_relat_1(X23))&(r2_hidden(esk5_1(X23),k3_relat_1(X23))|v6_relat_2(X23)|~v1_relat_1(X23)))&(esk4_1(X23)!=esk5_1(X23)|v6_relat_2(X23)|~v1_relat_1(X23)))&(~r2_hidden(k4_tarski(esk4_1(X23),esk5_1(X23)),X23)|v6_relat_2(X23)|~v1_relat_1(X23)))&(~r2_hidden(k4_tarski(esk5_1(X23),esk4_1(X23)),X23)|v6_relat_2(X23)|~v1_relat_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).
% 0.19/0.52  fof(c_0_10, negated_conjecture, (v1_relat_1(esk11_0)&(((v2_wellord1(esk11_0)&r2_hidden(esk9_0,k3_relat_1(esk11_0)))&r2_hidden(esk10_0,k3_relat_1(esk11_0)))&((~r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)|~r1_tarski(k1_wellord1(esk11_0,esk9_0),k1_wellord1(esk11_0,esk10_0)))&(r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)|r1_tarski(k1_wellord1(esk11_0,esk9_0),k1_wellord1(esk11_0,esk10_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.19/0.52  cnf(c_0_11, plain, (X2=X3|r2_hidden(k4_tarski(X2,X3),X1)|r2_hidden(k4_tarski(X3,X2),X1)|~v6_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r2_hidden(X3,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.52  cnf(c_0_12, negated_conjecture, (r2_hidden(esk10_0,k3_relat_1(esk11_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.52  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.52  fof(c_0_14, plain, ![X19]:((((((v1_relat_2(X19)|~v2_wellord1(X19)|~v1_relat_1(X19))&(v8_relat_2(X19)|~v2_wellord1(X19)|~v1_relat_1(X19)))&(v4_relat_2(X19)|~v2_wellord1(X19)|~v1_relat_1(X19)))&(v6_relat_2(X19)|~v2_wellord1(X19)|~v1_relat_1(X19)))&(v1_wellord1(X19)|~v2_wellord1(X19)|~v1_relat_1(X19)))&(~v1_relat_2(X19)|~v8_relat_2(X19)|~v4_relat_2(X19)|~v6_relat_2(X19)|~v1_wellord1(X19)|v2_wellord1(X19)|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 0.19/0.52  fof(c_0_15, plain, ![X11, X12, X13, X14, X15, X16, X17]:((((X14!=X12|~r2_hidden(X14,X13)|X13!=k1_wellord1(X11,X12)|~v1_relat_1(X11))&(r2_hidden(k4_tarski(X14,X12),X11)|~r2_hidden(X14,X13)|X13!=k1_wellord1(X11,X12)|~v1_relat_1(X11)))&(X15=X12|~r2_hidden(k4_tarski(X15,X12),X11)|r2_hidden(X15,X13)|X13!=k1_wellord1(X11,X12)|~v1_relat_1(X11)))&((~r2_hidden(esk2_3(X11,X16,X17),X17)|(esk2_3(X11,X16,X17)=X16|~r2_hidden(k4_tarski(esk2_3(X11,X16,X17),X16),X11))|X17=k1_wellord1(X11,X16)|~v1_relat_1(X11))&((esk2_3(X11,X16,X17)!=X16|r2_hidden(esk2_3(X11,X16,X17),X17)|X17=k1_wellord1(X11,X16)|~v1_relat_1(X11))&(r2_hidden(k4_tarski(esk2_3(X11,X16,X17),X16),X11)|r2_hidden(esk2_3(X11,X16,X17),X17)|X17=k1_wellord1(X11,X16)|~v1_relat_1(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.19/0.52  cnf(c_0_16, negated_conjecture, (X1=esk10_0|r2_hidden(k4_tarski(esk10_0,X1),esk11_0)|r2_hidden(k4_tarski(X1,esk10_0),esk11_0)|~v6_relat_2(esk11_0)|~r2_hidden(X1,k3_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])])).
% 0.19/0.52  cnf(c_0_17, plain, (v6_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.52  cnf(c_0_18, negated_conjecture, (v2_wellord1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.52  cnf(c_0_19, plain, (X1=X2|r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.52  cnf(c_0_20, negated_conjecture, (X1=esk10_0|r2_hidden(k4_tarski(X1,esk10_0),esk11_0)|r2_hidden(k4_tarski(esk10_0,X1),esk11_0)|~r2_hidden(X1,k3_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_13])])).
% 0.19/0.52  cnf(c_0_21, negated_conjecture, (r2_hidden(esk9_0,k3_relat_1(esk11_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.52  fof(c_0_22, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.52  cnf(c_0_23, plain, (X1=X2|r2_hidden(X1,k1_wellord1(X3,X2))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X2),X3)), inference(er,[status(thm)],[c_0_19])).
% 0.19/0.52  cnf(c_0_24, negated_conjecture, (esk10_0=esk9_0|r2_hidden(k4_tarski(esk10_0,esk9_0),esk11_0)|r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.52  cnf(c_0_25, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.52  cnf(c_0_26, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)|r1_tarski(k1_wellord1(esk11_0,esk9_0),k1_wellord1(esk11_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.52  cnf(c_0_27, negated_conjecture, (esk10_0=esk9_0|r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)|r2_hidden(esk10_0,k1_wellord1(esk11_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_13])])).
% 0.19/0.52  fof(c_0_28, plain, ![X30, X31, X32, X33, X34]:(((X30!=k3_relat_1(X31)|(~r2_hidden(X33,X30)|(~r2_hidden(k4_tarski(X34,X33),X31)|r2_hidden(X34,X30)))|(~v2_wellord1(X31)|~r1_tarski(X30,k3_relat_1(X31)))|~v1_relat_1(X31))&(~r2_hidden(X32,k3_relat_1(X31))|X30!=k1_wellord1(X31,X32)|(~r2_hidden(X33,X30)|(~r2_hidden(k4_tarski(X34,X33),X31)|r2_hidden(X34,X30)))|(~v2_wellord1(X31)|~r1_tarski(X30,k3_relat_1(X31)))|~v1_relat_1(X31)))&(((r2_hidden(esk8_2(X30,X31),k3_relat_1(X31))|X30=k3_relat_1(X31)|r2_hidden(esk6_2(X30,X31),X30)|(~v2_wellord1(X31)|~r1_tarski(X30,k3_relat_1(X31)))|~v1_relat_1(X31))&(X30=k1_wellord1(X31,esk8_2(X30,X31))|X30=k3_relat_1(X31)|r2_hidden(esk6_2(X30,X31),X30)|(~v2_wellord1(X31)|~r1_tarski(X30,k3_relat_1(X31)))|~v1_relat_1(X31)))&(((r2_hidden(esk8_2(X30,X31),k3_relat_1(X31))|X30=k3_relat_1(X31)|r2_hidden(k4_tarski(esk7_2(X30,X31),esk6_2(X30,X31)),X31)|(~v2_wellord1(X31)|~r1_tarski(X30,k3_relat_1(X31)))|~v1_relat_1(X31))&(X30=k1_wellord1(X31,esk8_2(X30,X31))|X30=k3_relat_1(X31)|r2_hidden(k4_tarski(esk7_2(X30,X31),esk6_2(X30,X31)),X31)|(~v2_wellord1(X31)|~r1_tarski(X30,k3_relat_1(X31)))|~v1_relat_1(X31)))&((r2_hidden(esk8_2(X30,X31),k3_relat_1(X31))|X30=k3_relat_1(X31)|~r2_hidden(esk7_2(X30,X31),X30)|(~v2_wellord1(X31)|~r1_tarski(X30,k3_relat_1(X31)))|~v1_relat_1(X31))&(X30=k1_wellord1(X31,esk8_2(X30,X31))|X30=k3_relat_1(X31)|~r2_hidden(esk7_2(X30,X31),X30)|(~v2_wellord1(X31)|~r1_tarski(X30,k3_relat_1(X31)))|~v1_relat_1(X31)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_wellord1])])])])])).
% 0.19/0.52  fof(c_0_29, plain, ![X28, X29]:(~v1_relat_1(X29)|r1_tarski(k1_wellord1(X29,X28),k3_relat_1(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_wellord1])])).
% 0.19/0.52  cnf(c_0_30, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)|r2_hidden(X1,k1_wellord1(esk11_0,esk10_0))|~r2_hidden(X1,k1_wellord1(esk11_0,esk9_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.52  cnf(c_0_31, negated_conjecture, (esk10_0=esk9_0|r2_hidden(esk10_0,k1_wellord1(esk11_0,esk9_0))|r2_hidden(esk9_0,k1_wellord1(esk11_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_27]), c_0_13])])).
% 0.19/0.52  cnf(c_0_32, plain, (r2_hidden(X5,X3)|~r2_hidden(X1,k3_relat_1(X2))|X3!=k1_wellord1(X2,X1)|~r2_hidden(X4,X3)|~r2_hidden(k4_tarski(X5,X4),X2)|~v2_wellord1(X2)|~r1_tarski(X3,k3_relat_1(X2))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.52  cnf(c_0_33, plain, (r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.52  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.52  cnf(c_0_35, plain, (X1!=X2|~r2_hidden(X1,X3)|X3!=k1_wellord1(X4,X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.52  cnf(c_0_36, negated_conjecture, (esk10_0=esk9_0|r2_hidden(esk9_0,k1_wellord1(esk11_0,esk10_0))|r2_hidden(esk10_0,k1_wellord1(esk11_0,esk10_0))|r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.52  cnf(c_0_37, plain, (r2_hidden(X1,k1_wellord1(X2,X3))|~v2_wellord1(X2)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,k1_wellord1(X2,X3))|~r2_hidden(X3,k3_relat_1(X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_33])).
% 0.19/0.52  cnf(c_0_38, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X1,k1_wellord1(X3,X2))), inference(er,[status(thm)],[c_0_34])).
% 0.19/0.52  cnf(c_0_39, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k1_wellord1(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).
% 0.19/0.52  cnf(c_0_40, negated_conjecture, (esk10_0=esk9_0|r2_hidden(esk10_0,k1_wellord1(esk11_0,esk10_0))|r2_hidden(esk9_0,k1_wellord1(esk11_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_36]), c_0_13])])).
% 0.19/0.52  cnf(c_0_41, plain, (r2_hidden(X1,k1_wellord1(X2,X3))|~v2_wellord1(X2)|~v1_relat_1(X2)|~r2_hidden(X4,k1_wellord1(X2,X3))|~r2_hidden(X1,k1_wellord1(X2,X4))|~r2_hidden(X3,k3_relat_1(X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.52  cnf(c_0_42, negated_conjecture, (esk10_0=esk9_0|r2_hidden(esk9_0,k1_wellord1(esk11_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_13])])).
% 0.19/0.52  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.52  cnf(c_0_44, negated_conjecture, (esk10_0=esk9_0|r2_hidden(X1,k1_wellord1(esk11_0,esk10_0))|~r2_hidden(X1,k1_wellord1(esk11_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_18]), c_0_13]), c_0_12])])).
% 0.19/0.52  cnf(c_0_45, negated_conjecture, (esk10_0=esk9_0|r1_tarski(X1,k1_wellord1(esk11_0,esk10_0))|~r2_hidden(esk1_2(X1,k1_wellord1(esk11_0,esk10_0)),k1_wellord1(esk11_0,esk9_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.52  cnf(c_0_46, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.52  cnf(c_0_47, negated_conjecture, (~r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)|~r1_tarski(k1_wellord1(esk11_0,esk9_0),k1_wellord1(esk11_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.52  cnf(c_0_48, negated_conjecture, (esk10_0=esk9_0|r1_tarski(k1_wellord1(esk11_0,esk9_0),k1_wellord1(esk11_0,esk10_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.52  cnf(c_0_49, negated_conjecture, (esk10_0=esk9_0|~r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.52  cnf(c_0_50, negated_conjecture, (esk10_0=esk9_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_38]), c_0_13])]), c_0_42])).
% 0.19/0.52  cnf(c_0_51, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_43, c_0_46])).
% 0.19/0.52  fof(c_0_52, plain, ![X20, X21]:((~v1_relat_2(X20)|(~r2_hidden(X21,k3_relat_1(X20))|r2_hidden(k4_tarski(X21,X21),X20))|~v1_relat_1(X20))&((r2_hidden(esk3_1(X20),k3_relat_1(X20))|v1_relat_2(X20)|~v1_relat_1(X20))&(~r2_hidden(k4_tarski(esk3_1(X20),esk3_1(X20)),X20)|v1_relat_2(X20)|~v1_relat_1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).
% 0.19/0.52  cnf(c_0_53, negated_conjecture, (~r2_hidden(k4_tarski(esk9_0,esk9_0),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_50]), c_0_50]), c_0_51])])).
% 0.19/0.52  cnf(c_0_54, plain, (r2_hidden(k4_tarski(X2,X2),X1)|~v1_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.52  cnf(c_0_55, negated_conjecture, (~v1_relat_2(esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_13]), c_0_21])])).
% 0.19/0.52  cnf(c_0_56, plain, (v1_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.52  cnf(c_0_57, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_18]), c_0_13])]), ['proof']).
% 0.19/0.52  # SZS output end CNFRefutation
% 0.19/0.52  # Proof object total steps             : 58
% 0.19/0.52  # Proof object clause steps            : 41
% 0.19/0.52  # Proof object formula steps           : 17
% 0.19/0.52  # Proof object conjectures             : 26
% 0.19/0.52  # Proof object clause conjectures      : 23
% 0.19/0.52  # Proof object formula conjectures     : 3
% 0.19/0.52  # Proof object initial clauses used    : 18
% 0.19/0.52  # Proof object initial formulas used   : 8
% 0.19/0.52  # Proof object generating inferences   : 18
% 0.19/0.52  # Proof object simplifying inferences  : 36
% 0.19/0.52  # Training examples: 0 positive, 0 negative
% 0.19/0.52  # Parsed axioms                        : 8
% 0.19/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.52  # Initial clauses                      : 39
% 0.19/0.52  # Removed in clause preprocessing      : 0
% 0.19/0.52  # Initial clauses in saturation        : 39
% 0.19/0.52  # Processed clauses                    : 404
% 0.19/0.52  # ...of these trivial                  : 0
% 0.19/0.52  # ...subsumed                          : 59
% 0.19/0.52  # ...remaining for further processing  : 345
% 0.19/0.52  # Other redundant clauses eliminated   : 6
% 0.19/0.52  # Clauses deleted for lack of memory   : 0
% 0.19/0.52  # Backward-subsumed                    : 7
% 0.19/0.52  # Backward-rewritten                   : 93
% 0.19/0.52  # Generated clauses                    : 976
% 0.19/0.52  # ...of the previous two non-trivial   : 963
% 0.19/0.52  # Contextual simplify-reflections      : 7
% 0.19/0.52  # Paramodulations                      : 962
% 0.19/0.52  # Factorizations                       : 4
% 0.19/0.52  # Equation resolutions                 : 6
% 0.19/0.52  # Propositional unsat checks           : 0
% 0.19/0.52  #    Propositional check models        : 0
% 0.19/0.52  #    Propositional check unsatisfiable : 0
% 0.19/0.52  #    Propositional clauses             : 0
% 0.19/0.52  #    Propositional clauses after purity: 0
% 0.19/0.52  #    Propositional unsat core size     : 0
% 0.19/0.52  #    Propositional preprocessing time  : 0.000
% 0.19/0.52  #    Propositional encoding time       : 0.000
% 0.19/0.52  #    Propositional solver time         : 0.000
% 0.19/0.52  #    Success case prop preproc time    : 0.000
% 0.19/0.52  #    Success case prop encoding time   : 0.000
% 0.19/0.52  #    Success case prop solver time     : 0.000
% 0.19/0.52  # Current number of processed clauses  : 235
% 0.19/0.52  #    Positive orientable unit clauses  : 6
% 0.19/0.52  #    Positive unorientable unit clauses: 0
% 0.19/0.52  #    Negative unit clauses             : 3
% 0.19/0.52  #    Non-unit-clauses                  : 226
% 0.19/0.52  # Current number of unprocessed clauses: 586
% 0.19/0.52  # ...number of literals in the above   : 4781
% 0.19/0.52  # Current number of archived formulas  : 0
% 0.19/0.52  # Current number of archived clauses   : 105
% 0.19/0.52  # Clause-clause subsumption calls (NU) : 69330
% 0.19/0.52  # Rec. Clause-clause subsumption calls : 592
% 0.19/0.52  # Non-unit clause-clause subsumptions  : 73
% 0.19/0.52  # Unit Clause-clause subsumption calls : 89
% 0.19/0.52  # Rewrite failures with RHS unbound    : 0
% 0.19/0.52  # BW rewrite match attempts            : 7
% 0.19/0.52  # BW rewrite match successes           : 1
% 0.19/0.52  # Condensation attempts                : 0
% 0.19/0.52  # Condensation successes               : 0
% 0.19/0.52  # Termbank termtop insertions          : 135167
% 0.19/0.52  
% 0.19/0.52  # -------------------------------------------------
% 0.19/0.52  # User time                : 0.174 s
% 0.19/0.52  # System time              : 0.009 s
% 0.19/0.52  # Total time               : 0.183 s
% 0.19/0.52  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
