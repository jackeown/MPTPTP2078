%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0703+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:04 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 198 expanded)
%              Number of clauses        :   32 (  79 expanded)
%              Number of leaves         :    4 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  183 ( 986 expanded)
%              Number of equality atoms :   29 ( 107 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t158_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
          & r1_tarski(X1,k2_relat_1(X3)) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d13_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( r2_hidden(X4,k1_relat_1(X1))
                & r2_hidden(k1_funct_1(X1,X4),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
            & r1_tarski(X1,k2_relat_1(X3)) )
         => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t158_funct_1])).

fof(c_0_5,plain,(
    ! [X19,X20,X21,X23,X24,X25,X27] :
      ( ( r2_hidden(esk3_3(X19,X20,X21),k1_relat_1(X19))
        | ~ r2_hidden(X21,X20)
        | X20 != k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( X21 = k1_funct_1(X19,esk3_3(X19,X20,X21))
        | ~ r2_hidden(X21,X20)
        | X20 != k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( ~ r2_hidden(X24,k1_relat_1(X19))
        | X23 != k1_funct_1(X19,X24)
        | r2_hidden(X23,X20)
        | X20 != k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( ~ r2_hidden(esk4_2(X19,X25),X25)
        | ~ r2_hidden(X27,k1_relat_1(X19))
        | esk4_2(X19,X25) != k1_funct_1(X19,X27)
        | X25 = k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( r2_hidden(esk5_2(X19,X25),k1_relat_1(X19))
        | r2_hidden(esk4_2(X19,X25),X25)
        | X25 = k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( esk4_2(X19,X25) = k1_funct_1(X19,esk5_2(X19,X25))
        | r2_hidden(esk4_2(X19,X25),X25)
        | X25 = k2_relat_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_6,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( ~ r1_tarski(X13,X14)
        | ~ r2_hidden(X15,X13)
        | r2_hidden(X15,X14) )
      & ( r2_hidden(esk2_2(X16,X17),X16)
        | r1_tarski(X16,X17) )
      & ( ~ r2_hidden(esk2_2(X16,X17),X17)
        | r1_tarski(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & v1_funct_1(esk8_0)
    & r1_tarski(k10_relat_1(esk8_0,esk6_0),k10_relat_1(esk8_0,esk7_0))
    & r1_tarski(esk6_0,k2_relat_1(esk8_0))
    & ~ r1_tarski(esk6_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(esk6_0,k2_relat_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( X1 = k1_funct_1(X2,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk8_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_20,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11] :
      ( ( r2_hidden(X8,k1_relat_1(X5))
        | ~ r2_hidden(X8,X7)
        | X7 != k10_relat_1(X5,X6)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( r2_hidden(k1_funct_1(X5,X8),X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k10_relat_1(X5,X6)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( ~ r2_hidden(X9,k1_relat_1(X5))
        | ~ r2_hidden(k1_funct_1(X5,X9),X6)
        | r2_hidden(X9,X7)
        | X7 != k10_relat_1(X5,X6)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( ~ r2_hidden(esk1_3(X5,X10,X11),X11)
        | ~ r2_hidden(esk1_3(X5,X10,X11),k1_relat_1(X5))
        | ~ r2_hidden(k1_funct_1(X5,esk1_3(X5,X10,X11)),X10)
        | X11 = k10_relat_1(X5,X10)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( r2_hidden(esk1_3(X5,X10,X11),k1_relat_1(X5))
        | r2_hidden(esk1_3(X5,X10,X11),X11)
        | X11 = k10_relat_1(X5,X10)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( r2_hidden(k1_funct_1(X5,esk1_3(X5,X10,X11)),X10)
        | r2_hidden(esk1_3(X5,X10,X11),X11)
        | X11 = k10_relat_1(X5,X10)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_12])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_3(esk8_0,k2_relat_1(esk8_0),X1),k1_relat_1(esk8_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_23,negated_conjecture,
    ( k1_funct_1(esk8_0,esk3_3(esk8_0,k2_relat_1(esk8_0),X1)) = X1
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X4 != k10_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk8_0,esk6_0),k10_relat_1(esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,esk3_3(esk8_0,k2_relat_1(esk8_0),X1)),k2_relat_1(esk8_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_15]),c_0_16])])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(esk8_0,esk3_3(esk8_0,k2_relat_1(esk8_0),esk2_2(esk6_0,esk7_0))) = esk2_2(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk8_0,esk7_0))
    | ~ r2_hidden(X1,k10_relat_1(esk8_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_26])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,esk7_0),k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_24])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,X1),esk7_0)
    | ~ r2_hidden(X1,k10_relat_1(esk8_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_15]),c_0_16])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk3_3(esk8_0,k2_relat_1(esk8_0),esk2_2(esk6_0,esk7_0)),k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_32]),c_0_15]),c_0_16])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,esk7_0),esk7_0)
    | ~ r2_hidden(esk3_3(esk8_0,k2_relat_1(esk8_0),esk2_2(esk6_0,esk7_0)),k10_relat_1(esk8_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_3(esk8_0,k2_relat_1(esk8_0),esk2_2(esk6_0,esk7_0)),k10_relat_1(esk8_0,X1))
    | ~ r2_hidden(esk2_2(esk6_0,esk7_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_28]),c_0_15]),c_0_16])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,esk7_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_24])])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_18]),
    [proof]).

%------------------------------------------------------------------------------
