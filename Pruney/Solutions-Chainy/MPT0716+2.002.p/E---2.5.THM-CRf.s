%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:43 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 242 expanded)
%              Number of clauses        :   37 ( 101 expanded)
%              Number of leaves         :    9 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  206 (1276 expanded)
%              Number of equality atoms :   18 (  59 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t171_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ! [X3] :
              ( r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))
            <=> ( r1_tarski(X3,k1_relat_1(X1))
                & r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(t158_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ! [X4] :
          ( v1_relat_1(X4)
         => ( ( r1_tarski(X3,X4)
              & r1_tarski(X1,X2) )
           => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))
              <=> ( r1_tarski(X3,k1_relat_1(X1))
                  & r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t171_funct_1])).

fof(c_0_10,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | k1_relat_1(k5_relat_1(X20,X21)) = k10_relat_1(X20,k1_relat_1(X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & ( ~ r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))
      | ~ r1_tarski(esk5_0,k1_relat_1(esk3_0))
      | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) )
    & ( r1_tarski(esk5_0,k1_relat_1(esk3_0))
      | r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))) )
    & ( r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))
      | r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

cnf(c_0_12,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk3_0,X1)) = k10_relat_1(esk3_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk5_0,k1_relat_1(esk3_0))
    | r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk3_0,esk4_0)) = k10_relat_1(esk3_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X22,X23,X24,X25,X26,X27,X28] :
      ( ( r2_hidden(X25,k1_relat_1(X22))
        | ~ r2_hidden(X25,X24)
        | X24 != k10_relat_1(X22,X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(k1_funct_1(X22,X25),X23)
        | ~ r2_hidden(X25,X24)
        | X24 != k10_relat_1(X22,X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(X26,k1_relat_1(X22))
        | ~ r2_hidden(k1_funct_1(X22,X26),X23)
        | r2_hidden(X26,X24)
        | X24 != k10_relat_1(X22,X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(esk2_3(X22,X27,X28),X28)
        | ~ r2_hidden(esk2_3(X22,X27,X28),k1_relat_1(X22))
        | ~ r2_hidden(k1_funct_1(X22,esk2_3(X22,X27,X28)),X27)
        | X28 = k10_relat_1(X22,X27)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(esk2_3(X22,X27,X28),k1_relat_1(X22))
        | r2_hidden(esk2_3(X22,X27,X28),X28)
        | X28 = k10_relat_1(X22,X27)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(k1_funct_1(X22,esk2_3(X22,X27,X28)),X27)
        | r2_hidden(esk2_3(X22,X27,X28),X28)
        | X28 = k10_relat_1(X22,X27)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | r1_tarski(esk5_0,k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X3 != k10_relat_1(X2,X4)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | r1_tarski(esk5_0,k1_relat_1(esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,X1),k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | r1_tarski(esk5_0,k1_relat_1(esk3_0))
    | r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_28,plain,(
    ! [X32,X33,X34] :
      ( ~ v1_relat_1(X34)
      | ~ v1_funct_1(X34)
      | ~ r1_tarski(X32,k1_relat_1(X34))
      | ~ r1_tarski(k9_relat_1(X34,X32),X33)
      | r1_tarski(X32,k10_relat_1(X34,X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,X1),k1_relat_1(esk3_0))
    | r1_tarski(esk5_0,k1_relat_1(esk3_0))
    | r1_tarski(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_13])])).

cnf(c_0_31,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk5_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))
    | r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_34,plain,(
    ! [X16,X17,X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | ~ r1_tarski(X18,X19)
      | ~ r1_tarski(X16,X17)
      | r1_tarski(k9_relat_1(X18,X16),k9_relat_1(X19,X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_relat_1])])])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk5_0,k10_relat_1(esk3_0,X1))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_27]),c_0_13])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))
    | r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_18])).

fof(c_0_37,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_38,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | r1_tarski(k9_relat_1(X31,k10_relat_1(X31,X30)),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_39,plain,
    ( r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X4))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))
    | ~ r1_tarski(esk5_0,k1_relat_1(esk3_0))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_43,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_44,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k9_relat_1(X1,esk5_0),k9_relat_1(X2,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))
    | ~ r1_tarski(esk5_0,k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_18])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_27]),c_0_13])])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k9_relat_1(X1,esk5_0),k9_relat_1(X1,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_32])])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk5_0),k9_relat_1(esk3_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_13])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_40])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:52:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.48  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.20/0.48  # and selection function SelectNewComplexAHP.
% 0.20/0.48  #
% 0.20/0.48  # Preprocessing time       : 0.027 s
% 0.20/0.48  # Presaturation interreduction done
% 0.20/0.48  
% 0.20/0.48  # Proof found!
% 0.20/0.48  # SZS status Theorem
% 0.20/0.48  # SZS output start CNFRefutation
% 0.20/0.48  fof(t171_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 0.20/0.48  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 0.20/0.48  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.48  fof(d13_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k1_relat_1(X1))&r2_hidden(k1_funct_1(X1,X4),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_funct_1)).
% 0.20/0.48  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 0.20/0.48  fof(t158_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 0.20/0.48  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.48  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.20/0.48  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.48  fof(c_0_9, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t171_funct_1])).
% 0.20/0.48  fof(c_0_10, plain, ![X20, X21]:(~v1_relat_1(X20)|(~v1_relat_1(X21)|k1_relat_1(k5_relat_1(X20,X21))=k10_relat_1(X20,k1_relat_1(X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.20/0.48  fof(c_0_11, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((~r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))|(~r1_tarski(esk5_0,k1_relat_1(esk3_0))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))))&((r1_tarski(esk5_0,k1_relat_1(esk3_0))|r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))))&(r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))|r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.20/0.48  cnf(c_0_12, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.48  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.48  cnf(c_0_14, negated_conjecture, (k1_relat_1(k5_relat_1(esk3_0,X1))=k10_relat_1(esk3_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.48  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.48  fof(c_0_16, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.48  cnf(c_0_17, negated_conjecture, (r1_tarski(esk5_0,k1_relat_1(esk3_0))|r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.48  cnf(c_0_18, negated_conjecture, (k1_relat_1(k5_relat_1(esk3_0,esk4_0))=k10_relat_1(esk3_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.48  fof(c_0_19, plain, ![X22, X23, X24, X25, X26, X27, X28]:((((r2_hidden(X25,k1_relat_1(X22))|~r2_hidden(X25,X24)|X24!=k10_relat_1(X22,X23)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(r2_hidden(k1_funct_1(X22,X25),X23)|~r2_hidden(X25,X24)|X24!=k10_relat_1(X22,X23)|(~v1_relat_1(X22)|~v1_funct_1(X22))))&(~r2_hidden(X26,k1_relat_1(X22))|~r2_hidden(k1_funct_1(X22,X26),X23)|r2_hidden(X26,X24)|X24!=k10_relat_1(X22,X23)|(~v1_relat_1(X22)|~v1_funct_1(X22))))&((~r2_hidden(esk2_3(X22,X27,X28),X28)|(~r2_hidden(esk2_3(X22,X27,X28),k1_relat_1(X22))|~r2_hidden(k1_funct_1(X22,esk2_3(X22,X27,X28)),X27))|X28=k10_relat_1(X22,X27)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&((r2_hidden(esk2_3(X22,X27,X28),k1_relat_1(X22))|r2_hidden(esk2_3(X22,X27,X28),X28)|X28=k10_relat_1(X22,X27)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(r2_hidden(k1_funct_1(X22,esk2_3(X22,X27,X28)),X27)|r2_hidden(esk2_3(X22,X27,X28),X28)|X28=k10_relat_1(X22,X27)|(~v1_relat_1(X22)|~v1_funct_1(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).
% 0.20/0.48  cnf(c_0_20, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_21, negated_conjecture, (r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|r1_tarski(esk5_0,k1_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.48  cnf(c_0_22, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,X3)|X3!=k10_relat_1(X2,X4)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.48  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|r1_tarski(esk5_0,k1_relat_1(esk3_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.48  cnf(c_0_24, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_25, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k10_relat_1(X2,X3))), inference(er,[status(thm)],[c_0_22])).
% 0.20/0.48  cnf(c_0_26, negated_conjecture, (r2_hidden(esk1_2(esk5_0,X1),k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|r1_tarski(esk5_0,k1_relat_1(esk3_0))|r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.48  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.48  fof(c_0_28, plain, ![X32, X33, X34]:(~v1_relat_1(X34)|~v1_funct_1(X34)|(~r1_tarski(X32,k1_relat_1(X34))|~r1_tarski(k9_relat_1(X34,X32),X33)|r1_tarski(X32,k10_relat_1(X34,X33)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.20/0.48  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_2(esk5_0,X1),k1_relat_1(esk3_0))|r1_tarski(esk5_0,k1_relat_1(esk3_0))|r1_tarski(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_13])])).
% 0.20/0.48  cnf(c_0_31, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.48  cnf(c_0_32, negated_conjecture, (r1_tarski(esk5_0,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.48  cnf(c_0_33, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))|r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.48  fof(c_0_34, plain, ![X16, X17, X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|(~r1_tarski(X18,X19)|~r1_tarski(X16,X17)|r1_tarski(k9_relat_1(X18,X16),k9_relat_1(X19,X17))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_relat_1])])])).
% 0.20/0.48  cnf(c_0_35, negated_conjecture, (r1_tarski(esk5_0,k10_relat_1(esk3_0,X1))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_27]), c_0_13])])).
% 0.20/0.48  cnf(c_0_36, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))|r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))), inference(rw,[status(thm)],[c_0_33, c_0_18])).
% 0.20/0.48  fof(c_0_37, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.48  fof(c_0_38, plain, ![X30, X31]:(~v1_relat_1(X31)|~v1_funct_1(X31)|r1_tarski(k9_relat_1(X31,k10_relat_1(X31,X30)),X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.20/0.48  cnf(c_0_39, plain, (r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X4))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.48  cnf(c_0_40, negated_conjecture, (r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.48  cnf(c_0_41, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.48  cnf(c_0_42, negated_conjecture, (~r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))|~r1_tarski(esk5_0,k1_relat_1(esk3_0))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.48  fof(c_0_43, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X14,X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.48  cnf(c_0_44, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.48  cnf(c_0_45, negated_conjecture, (r1_tarski(k9_relat_1(X1,esk5_0),k9_relat_1(X2,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.48  cnf(c_0_46, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_41])).
% 0.20/0.48  cnf(c_0_47, negated_conjecture, (~r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))|~r1_tarski(esk5_0,k1_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_42, c_0_18])).
% 0.20/0.48  cnf(c_0_48, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.48  cnf(c_0_49, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_27]), c_0_13])])).
% 0.20/0.48  cnf(c_0_50, negated_conjecture, (r1_tarski(k9_relat_1(X1,esk5_0),k9_relat_1(X1,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.48  cnf(c_0_51, negated_conjecture, (~r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_32])])).
% 0.20/0.48  cnf(c_0_52, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X1,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.48  cnf(c_0_53, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk5_0),k9_relat_1(esk3_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))), inference(spm,[status(thm)],[c_0_50, c_0_13])).
% 0.20/0.48  cnf(c_0_54, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_40])])).
% 0.20/0.48  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), ['proof']).
% 0.20/0.48  # SZS output end CNFRefutation
% 0.20/0.48  # Proof object total steps             : 56
% 0.20/0.48  # Proof object clause steps            : 37
% 0.20/0.48  # Proof object formula steps           : 19
% 0.20/0.48  # Proof object conjectures             : 28
% 0.20/0.48  # Proof object clause conjectures      : 25
% 0.20/0.48  # Proof object formula conjectures     : 3
% 0.20/0.48  # Proof object initial clauses used    : 16
% 0.20/0.48  # Proof object initial formulas used   : 9
% 0.20/0.48  # Proof object generating inferences   : 14
% 0.20/0.48  # Proof object simplifying inferences  : 18
% 0.20/0.48  # Training examples: 0 positive, 0 negative
% 0.20/0.48  # Parsed axioms                        : 9
% 0.20/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.48  # Initial clauses                      : 24
% 0.20/0.48  # Removed in clause preprocessing      : 0
% 0.20/0.48  # Initial clauses in saturation        : 24
% 0.20/0.48  # Processed clauses                    : 697
% 0.20/0.48  # ...of these trivial                  : 38
% 0.20/0.48  # ...subsumed                          : 105
% 0.20/0.48  # ...remaining for further processing  : 554
% 0.20/0.48  # Other redundant clauses eliminated   : 5
% 0.20/0.48  # Clauses deleted for lack of memory   : 0
% 0.20/0.48  # Backward-subsumed                    : 1
% 0.20/0.48  # Backward-rewritten                   : 112
% 0.20/0.48  # Generated clauses                    : 4761
% 0.20/0.48  # ...of the previous two non-trivial   : 4461
% 0.20/0.48  # Contextual simplify-reflections      : 2
% 0.20/0.48  # Paramodulations                      : 4752
% 0.20/0.48  # Factorizations                       : 4
% 0.20/0.48  # Equation resolutions                 : 5
% 0.20/0.48  # Propositional unsat checks           : 0
% 0.20/0.48  #    Propositional check models        : 0
% 0.20/0.48  #    Propositional check unsatisfiable : 0
% 0.20/0.48  #    Propositional clauses             : 0
% 0.20/0.48  #    Propositional clauses after purity: 0
% 0.20/0.48  #    Propositional unsat core size     : 0
% 0.20/0.48  #    Propositional preprocessing time  : 0.000
% 0.20/0.48  #    Propositional encoding time       : 0.000
% 0.20/0.48  #    Propositional solver time         : 0.000
% 0.20/0.48  #    Success case prop preproc time    : 0.000
% 0.20/0.48  #    Success case prop encoding time   : 0.000
% 0.20/0.48  #    Success case prop solver time     : 0.000
% 0.20/0.48  # Current number of processed clauses  : 413
% 0.20/0.48  #    Positive orientable unit clauses  : 116
% 0.20/0.48  #    Positive unorientable unit clauses: 0
% 0.20/0.48  #    Negative unit clauses             : 1
% 0.20/0.48  #    Non-unit-clauses                  : 296
% 0.20/0.48  # Current number of unprocessed clauses: 3741
% 0.20/0.48  # ...number of literals in the above   : 7869
% 0.20/0.48  # Current number of archived formulas  : 0
% 0.20/0.48  # Current number of archived clauses   : 136
% 0.20/0.48  # Clause-clause subsumption calls (NU) : 7453
% 0.20/0.48  # Rec. Clause-clause subsumption calls : 5669
% 0.20/0.48  # Non-unit clause-clause subsumptions  : 108
% 0.20/0.48  # Unit Clause-clause subsumption calls : 370
% 0.20/0.48  # Rewrite failures with RHS unbound    : 0
% 0.20/0.48  # BW rewrite match attempts            : 293
% 0.20/0.48  # BW rewrite match successes           : 20
% 0.20/0.48  # Condensation attempts                : 0
% 0.20/0.48  # Condensation successes               : 0
% 0.20/0.48  # Termbank termtop insertions          : 121059
% 0.20/0.48  
% 0.20/0.48  # -------------------------------------------------
% 0.20/0.48  # User time                : 0.126 s
% 0.20/0.48  # System time              : 0.010 s
% 0.20/0.48  # Total time               : 0.136 s
% 0.20/0.48  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
