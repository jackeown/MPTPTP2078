%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:39 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 892 expanded)
%              Number of clauses        :   57 ( 320 expanded)
%              Number of leaves         :   12 ( 212 expanded)
%              Depth                    :   17
%              Number of atoms          :  306 (5145 expanded)
%              Number of equality atoms :   68 ( 760 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(k5_relat_1(X2,X1))
              & k2_relat_1(X2) = k1_relat_1(X1) )
           => ( v2_funct_1(X2)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(t47_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(k5_relat_1(X2,X1))
              & r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) )
           => v2_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t22_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
           => k1_funct_1(k5_relat_1(X3,X2),X1) = k1_funct_1(X2,k1_funct_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(k5_relat_1(X2,X1))
                & k2_relat_1(X2) = k1_relat_1(X1) )
             => ( v2_funct_1(X2)
                & v2_funct_1(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_funct_1])).

fof(c_0_13,plain,(
    ! [X44,X45] :
      ( ~ v1_relat_1(X44)
      | ~ v1_funct_1(X44)
      | ~ v1_relat_1(X45)
      | ~ v1_funct_1(X45)
      | ~ v2_funct_1(k5_relat_1(X45,X44))
      | ~ r1_tarski(k2_relat_1(X45),k1_relat_1(X44))
      | v2_funct_1(X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_funct_1])])])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & v1_funct_1(esk9_0)
    & v1_relat_1(esk10_0)
    & v1_funct_1(esk10_0)
    & v2_funct_1(k5_relat_1(esk10_0,esk9_0))
    & k2_relat_1(esk10_0) = k1_relat_1(esk9_0)
    & ( ~ v2_funct_1(esk10_0)
      | ~ v2_funct_1(esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_16,plain,(
    ! [X18,X19,X20,X22,X23,X24,X25,X27] :
      ( ( ~ r2_hidden(X20,X19)
        | r2_hidden(k4_tarski(esk4_3(X18,X19,X20),X20),X18)
        | X19 != k2_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X23,X22),X18)
        | r2_hidden(X22,X19)
        | X19 != k2_relat_1(X18) )
      & ( ~ r2_hidden(esk5_2(X24,X25),X25)
        | ~ r2_hidden(k4_tarski(X27,esk5_2(X24,X25)),X24)
        | X25 = k2_relat_1(X24) )
      & ( r2_hidden(esk5_2(X24,X25),X25)
        | r2_hidden(k4_tarski(esk6_2(X24,X25),esk5_2(X24,X25)),X24)
        | X25 = k2_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_17,plain,
    ( v2_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(k5_relat_1(X2,X1))
    | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk10_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( k2_relat_1(esk10_0) = k1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( v2_funct_1(esk10_0)
    | ~ r1_tarski(k1_relat_1(esk9_0),k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X31] :
      ( ~ v1_relat_1(X31)
      | k10_relat_1(X31,k2_relat_1(X31)) = k1_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X34,X35,X36] :
      ( ( ~ v2_funct_1(X34)
        | ~ r2_hidden(X35,k1_relat_1(X34))
        | ~ r2_hidden(X36,k1_relat_1(X34))
        | k1_funct_1(X34,X35) != k1_funct_1(X34,X36)
        | X35 = X36
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( r2_hidden(esk7_1(X34),k1_relat_1(X34))
        | v2_funct_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( r2_hidden(esk8_1(X34),k1_relat_1(X34))
        | v2_funct_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( k1_funct_1(X34,esk7_1(X34)) = k1_funct_1(X34,esk8_1(X34))
        | v2_funct_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( esk7_1(X34) != esk8_1(X34)
        | v2_funct_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_funct_1(esk10_0)
    | ~ v2_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,negated_conjecture,
    ( v2_funct_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])])).

fof(c_0_33,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X32)
      | ~ v1_relat_1(X33)
      | k1_relat_1(k5_relat_1(X32,X33)) = k10_relat_1(X32,k1_relat_1(X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

cnf(c_0_34,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X46,X47,X48] :
      ( ( r2_hidden(X46,k1_relat_1(X48))
        | ~ r2_hidden(k4_tarski(X46,X47),X48)
        | ~ v1_relat_1(X48)
        | ~ v1_funct_1(X48) )
      & ( X47 = k1_funct_1(X48,X46)
        | ~ r2_hidden(k4_tarski(X46,X47),X48)
        | ~ v1_relat_1(X48)
        | ~ v1_funct_1(X48) )
      & ( ~ r2_hidden(X46,k1_relat_1(X48))
        | X47 != k1_funct_1(X48,X46)
        | r2_hidden(k4_tarski(X46,X47),X48)
        | ~ v1_relat_1(X48)
        | ~ v1_funct_1(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_36,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_3(esk10_0,k1_relat_1(esk9_0),X1),X1),esk10_0)
    | ~ r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_38,plain,
    ( r2_hidden(esk8_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_funct_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])])).

cnf(c_0_40,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( k10_relat_1(esk10_0,k1_relat_1(esk9_0)) = k1_relat_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_23]),c_0_21])])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_3(esk10_0,k1_relat_1(esk9_0),esk8_1(esk9_0)),esk8_1(esk9_0)),esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_20]),c_0_22])]),c_0_39])).

cnf(c_0_45,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk10_0,esk9_0)) = k1_relat_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_22]),c_0_21])])).

fof(c_0_47,plain,(
    ! [X39,X40] :
      ( ( v1_relat_1(k5_relat_1(X39,X40))
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39)
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40) )
      & ( v1_funct_1(k5_relat_1(X39,X40))
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39)
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

fof(c_0_48,plain,(
    ! [X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( ~ r2_hidden(X9,X8)
        | r2_hidden(k4_tarski(X9,esk1_3(X7,X8,X9)),X7)
        | X8 != k1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(X11,X12),X7)
        | r2_hidden(X11,X8)
        | X8 != k1_relat_1(X7) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | ~ r2_hidden(k4_tarski(esk2_2(X13,X14),X16),X13)
        | X14 = k1_relat_1(X13) )
      & ( r2_hidden(esk2_2(X13,X14),X14)
        | r2_hidden(k4_tarski(esk2_2(X13,X14),esk3_2(X13,X14)),X13)
        | X14 = k1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_49,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk8_1(esk9_0),k1_relat_1(esk9_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(k5_relat_1(esk10_0,esk9_0),X1) != k1_funct_1(k5_relat_1(esk10_0,esk9_0),X2)
    | ~ v1_funct_1(k5_relat_1(esk10_0,esk9_0))
    | ~ v1_relat_1(k5_relat_1(esk10_0,esk9_0))
    | ~ r2_hidden(X2,k1_relat_1(esk10_0))
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_18])])).

cnf(c_0_52,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_53,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X29)
      | ~ v1_relat_1(X30)
      | v1_relat_1(k5_relat_1(X29,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_55,plain,(
    ! [X41,X42,X43] :
      ( ~ v1_relat_1(X42)
      | ~ v1_funct_1(X42)
      | ~ v1_relat_1(X43)
      | ~ v1_funct_1(X43)
      | ~ r2_hidden(X41,k1_relat_1(k5_relat_1(X43,X42)))
      | k1_funct_1(k5_relat_1(X43,X42),X41) = k1_funct_1(X42,k1_funct_1(X43,X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_1(esk9_0),k1_funct_1(esk9_0,esk8_1(esk9_0))),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_20]),c_0_22])])).

cnf(c_0_57,plain,
    ( k1_funct_1(X1,esk7_1(X1)) = k1_funct_1(X1,esk8_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_58,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(k5_relat_1(esk10_0,esk9_0),X1) != k1_funct_1(k5_relat_1(esk10_0,esk9_0),X2)
    | ~ v1_relat_1(k5_relat_1(esk10_0,esk9_0))
    | ~ r2_hidden(X2,k1_relat_1(esk10_0))
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_20]),c_0_19]),c_0_22]),c_0_21])])).

cnf(c_0_59,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_61,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_1(esk9_0),k1_funct_1(esk9_0,esk7_1(esk9_0))),esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_20]),c_0_22])]),c_0_39])).

cnf(c_0_64,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(k5_relat_1(esk10_0,esk9_0),X1) != k1_funct_1(k5_relat_1(esk10_0,esk9_0),X2)
    | ~ r2_hidden(X2,k1_relat_1(esk10_0))
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_22]),c_0_21])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk4_3(esk10_0,k1_relat_1(esk9_0),esk8_1(esk9_0)),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_44])).

cnf(c_0_66,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk10_0,esk9_0),X1) = k1_funct_1(esk9_0,k1_funct_1(esk10_0,X1))
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_46]),c_0_19]),c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_67,negated_conjecture,
    ( k1_funct_1(esk10_0,esk4_3(esk10_0,k1_relat_1(esk9_0),esk8_1(esk9_0))) = esk8_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_44]),c_0_19]),c_0_21])])).

cnf(c_0_68,negated_conjecture,
    ( k1_funct_1(esk9_0,esk8_1(esk9_0)) = k1_funct_1(esk9_0,esk7_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_20]),c_0_22])])).

cnf(c_0_69,plain,
    ( r2_hidden(esk7_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_70,negated_conjecture,
    ( X1 = esk4_3(esk10_0,k1_relat_1(esk9_0),esk8_1(esk9_0))
    | k1_funct_1(k5_relat_1(esk10_0,esk9_0),X1) != k1_funct_1(k5_relat_1(esk10_0,esk9_0),esk4_3(esk10_0,k1_relat_1(esk9_0),esk8_1(esk9_0)))
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk10_0,esk9_0),esk4_3(esk10_0,k1_relat_1(esk9_0),esk8_1(esk9_0))) = k1_funct_1(esk9_0,esk7_1(esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_65]),c_0_67]),c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_3(esk10_0,k1_relat_1(esk9_0),esk7_1(esk9_0)),esk7_1(esk9_0)),esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_69]),c_0_20]),c_0_22])]),c_0_39])).

cnf(c_0_73,negated_conjecture,
    ( X1 = esk4_3(esk10_0,k1_relat_1(esk9_0),esk8_1(esk9_0))
    | k1_funct_1(k5_relat_1(esk10_0,esk9_0),X1) != k1_funct_1(esk9_0,esk7_1(esk9_0))
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk4_3(esk10_0,k1_relat_1(esk9_0),esk7_1(esk9_0)),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( k1_funct_1(esk10_0,esk4_3(esk10_0,k1_relat_1(esk9_0),esk7_1(esk9_0))) = esk7_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_72]),c_0_19]),c_0_21])])).

cnf(c_0_76,negated_conjecture,
    ( esk4_3(esk10_0,k1_relat_1(esk9_0),esk8_1(esk9_0)) = esk4_3(esk10_0,k1_relat_1(esk9_0),esk7_1(esk9_0))
    | k1_funct_1(k5_relat_1(esk10_0,esk9_0),esk4_3(esk10_0,k1_relat_1(esk9_0),esk7_1(esk9_0))) != k1_funct_1(esk9_0,esk7_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk10_0,esk9_0),esk4_3(esk10_0,k1_relat_1(esk9_0),esk7_1(esk9_0))) = k1_funct_1(esk9_0,esk7_1(esk9_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_74]),c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( esk4_3(esk10_0,k1_relat_1(esk9_0),esk8_1(esk9_0)) = esk4_3(esk10_0,k1_relat_1(esk9_0),esk7_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_79,plain,
    ( v2_funct_1(X1)
    | esk7_1(X1) != esk8_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_80,negated_conjecture,
    ( esk8_1(esk9_0) = esk7_1(esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_78]),c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_20]),c_0_22])]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.13/0.38  # and selection function SelectNewComplexAHPNS.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t48_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&k2_relat_1(X2)=k1_relat_1(X1))=>(v2_funct_1(X2)&v2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 0.13/0.38  fof(t47_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&r1_tarski(k2_relat_1(X2),k1_relat_1(X1)))=>v2_funct_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.13/0.38  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.13/0.38  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 0.13/0.38  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 0.13/0.38  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.13/0.38  fof(fc2_funct_1, axiom, ![X1, X2]:((((v1_relat_1(X1)&v1_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v1_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 0.13/0.38  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.13/0.38  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.13/0.38  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&k2_relat_1(X2)=k1_relat_1(X1))=>(v2_funct_1(X2)&v2_funct_1(X1)))))), inference(assume_negation,[status(cth)],[t48_funct_1])).
% 0.13/0.38  fof(c_0_13, plain, ![X44, X45]:(~v1_relat_1(X44)|~v1_funct_1(X44)|(~v1_relat_1(X45)|~v1_funct_1(X45)|(~v2_funct_1(k5_relat_1(X45,X44))|~r1_tarski(k2_relat_1(X45),k1_relat_1(X44))|v2_funct_1(X45)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_funct_1])])])).
% 0.13/0.38  fof(c_0_14, negated_conjecture, ((v1_relat_1(esk9_0)&v1_funct_1(esk9_0))&((v1_relat_1(esk10_0)&v1_funct_1(esk10_0))&((v2_funct_1(k5_relat_1(esk10_0,esk9_0))&k2_relat_1(esk10_0)=k1_relat_1(esk9_0))&(~v2_funct_1(esk10_0)|~v2_funct_1(esk9_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.13/0.38  fof(c_0_15, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  fof(c_0_16, plain, ![X18, X19, X20, X22, X23, X24, X25, X27]:(((~r2_hidden(X20,X19)|r2_hidden(k4_tarski(esk4_3(X18,X19,X20),X20),X18)|X19!=k2_relat_1(X18))&(~r2_hidden(k4_tarski(X23,X22),X18)|r2_hidden(X22,X19)|X19!=k2_relat_1(X18)))&((~r2_hidden(esk5_2(X24,X25),X25)|~r2_hidden(k4_tarski(X27,esk5_2(X24,X25)),X24)|X25=k2_relat_1(X24))&(r2_hidden(esk5_2(X24,X25),X25)|r2_hidden(k4_tarski(esk6_2(X24,X25),esk5_2(X24,X25)),X24)|X25=k2_relat_1(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.13/0.38  cnf(c_0_17, plain, (v2_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(k5_relat_1(X2,X1))|~r1_tarski(k2_relat_1(X2),k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (v2_funct_1(k5_relat_1(esk10_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (k2_relat_1(esk10_0)=k1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_24, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_25, plain, (r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (v2_funct_1(esk10_0)|~r1_tarski(k1_relat_1(esk9_0),k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])])).
% 0.13/0.38  cnf(c_0_27, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_24])).
% 0.13/0.38  fof(c_0_28, plain, ![X31]:(~v1_relat_1(X31)|k10_relat_1(X31,k2_relat_1(X31))=k1_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.13/0.38  cnf(c_0_29, plain, (r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_25])).
% 0.13/0.38  fof(c_0_30, plain, ![X34, X35, X36]:((~v2_funct_1(X34)|(~r2_hidden(X35,k1_relat_1(X34))|~r2_hidden(X36,k1_relat_1(X34))|k1_funct_1(X34,X35)!=k1_funct_1(X34,X36)|X35=X36)|(~v1_relat_1(X34)|~v1_funct_1(X34)))&((((r2_hidden(esk7_1(X34),k1_relat_1(X34))|v2_funct_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34)))&(r2_hidden(esk8_1(X34),k1_relat_1(X34))|v2_funct_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34))))&(k1_funct_1(X34,esk7_1(X34))=k1_funct_1(X34,esk8_1(X34))|v2_funct_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34))))&(esk7_1(X34)!=esk8_1(X34)|v2_funct_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (~v2_funct_1(esk10_0)|~v2_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (v2_funct_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27])])).
% 0.13/0.38  fof(c_0_33, plain, ![X32, X33]:(~v1_relat_1(X32)|(~v1_relat_1(X33)|k1_relat_1(k5_relat_1(X32,X33))=k10_relat_1(X32,k1_relat_1(X33)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.13/0.38  cnf(c_0_34, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  fof(c_0_35, plain, ![X46, X47, X48]:(((r2_hidden(X46,k1_relat_1(X48))|~r2_hidden(k4_tarski(X46,X47),X48)|(~v1_relat_1(X48)|~v1_funct_1(X48)))&(X47=k1_funct_1(X48,X46)|~r2_hidden(k4_tarski(X46,X47),X48)|(~v1_relat_1(X48)|~v1_funct_1(X48))))&(~r2_hidden(X46,k1_relat_1(X48))|X47!=k1_funct_1(X48,X46)|r2_hidden(k4_tarski(X46,X47),X48)|(~v1_relat_1(X48)|~v1_funct_1(X48)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.13/0.38  cnf(c_0_36, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(esk4_3(esk10_0,k1_relat_1(esk9_0),X1),X1),esk10_0)|~r2_hidden(X1,k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_29, c_0_23])).
% 0.13/0.38  cnf(c_0_38, plain, (r2_hidden(esk8_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (~v2_funct_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32])])).
% 0.13/0.38  cnf(c_0_40, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (k10_relat_1(esk10_0,k1_relat_1(esk9_0))=k1_relat_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_23]), c_0_21])])).
% 0.13/0.38  cnf(c_0_42, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_43, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (r2_hidden(k4_tarski(esk4_3(esk10_0,k1_relat_1(esk9_0),esk8_1(esk9_0)),esk8_1(esk9_0)),esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_20]), c_0_22])]), c_0_39])).
% 0.13/0.38  cnf(c_0_45, plain, (X2=X3|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))|k1_funct_1(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (k1_relat_1(k5_relat_1(esk10_0,esk9_0))=k1_relat_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_22]), c_0_21])])).
% 0.13/0.38  fof(c_0_47, plain, ![X39, X40]:((v1_relat_1(k5_relat_1(X39,X40))|(~v1_relat_1(X39)|~v1_funct_1(X39)|~v1_relat_1(X40)|~v1_funct_1(X40)))&(v1_funct_1(k5_relat_1(X39,X40))|(~v1_relat_1(X39)|~v1_funct_1(X39)|~v1_relat_1(X40)|~v1_funct_1(X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).
% 0.13/0.38  fof(c_0_48, plain, ![X7, X8, X9, X11, X12, X13, X14, X16]:(((~r2_hidden(X9,X8)|r2_hidden(k4_tarski(X9,esk1_3(X7,X8,X9)),X7)|X8!=k1_relat_1(X7))&(~r2_hidden(k4_tarski(X11,X12),X7)|r2_hidden(X11,X8)|X8!=k1_relat_1(X7)))&((~r2_hidden(esk2_2(X13,X14),X14)|~r2_hidden(k4_tarski(esk2_2(X13,X14),X16),X13)|X14=k1_relat_1(X13))&(r2_hidden(esk2_2(X13,X14),X14)|r2_hidden(k4_tarski(esk2_2(X13,X14),esk3_2(X13,X14)),X13)|X14=k1_relat_1(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.13/0.38  cnf(c_0_49, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_42])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (r2_hidden(esk8_1(esk9_0),k1_relat_1(esk9_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_23])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (X1=X2|k1_funct_1(k5_relat_1(esk10_0,esk9_0),X1)!=k1_funct_1(k5_relat_1(esk10_0,esk9_0),X2)|~v1_funct_1(k5_relat_1(esk10_0,esk9_0))|~v1_relat_1(k5_relat_1(esk10_0,esk9_0))|~r2_hidden(X2,k1_relat_1(esk10_0))|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_18])])).
% 0.13/0.38  cnf(c_0_52, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.38  fof(c_0_53, plain, ![X29, X30]:(~v1_relat_1(X29)|~v1_relat_1(X30)|v1_relat_1(k5_relat_1(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.13/0.38  cnf(c_0_54, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.38  fof(c_0_55, plain, ![X41, X42, X43]:(~v1_relat_1(X42)|~v1_funct_1(X42)|(~v1_relat_1(X43)|~v1_funct_1(X43)|(~r2_hidden(X41,k1_relat_1(k5_relat_1(X43,X42)))|k1_funct_1(k5_relat_1(X43,X42),X41)=k1_funct_1(X42,k1_funct_1(X43,X41))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (r2_hidden(k4_tarski(esk8_1(esk9_0),k1_funct_1(esk9_0,esk8_1(esk9_0))),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_20]), c_0_22])])).
% 0.13/0.38  cnf(c_0_57, plain, (k1_funct_1(X1,esk7_1(X1))=k1_funct_1(X1,esk8_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (X1=X2|k1_funct_1(k5_relat_1(esk10_0,esk9_0),X1)!=k1_funct_1(k5_relat_1(esk10_0,esk9_0),X2)|~v1_relat_1(k5_relat_1(esk10_0,esk9_0))|~r2_hidden(X2,k1_relat_1(esk10_0))|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_20]), c_0_19]), c_0_22]), c_0_21])])).
% 0.13/0.38  cnf(c_0_59, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.38  cnf(c_0_60, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_54])).
% 0.13/0.38  cnf(c_0_61, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.13/0.38  cnf(c_0_62, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (r2_hidden(k4_tarski(esk8_1(esk9_0),k1_funct_1(esk9_0,esk7_1(esk9_0))),esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_20]), c_0_22])]), c_0_39])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (X1=X2|k1_funct_1(k5_relat_1(esk10_0,esk9_0),X1)!=k1_funct_1(k5_relat_1(esk10_0,esk9_0),X2)|~r2_hidden(X2,k1_relat_1(esk10_0))|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_22]), c_0_21])])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (r2_hidden(esk4_3(esk10_0,k1_relat_1(esk9_0),esk8_1(esk9_0)),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_60, c_0_44])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (k1_funct_1(k5_relat_1(esk10_0,esk9_0),X1)=k1_funct_1(esk9_0,k1_funct_1(esk10_0,X1))|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_46]), c_0_19]), c_0_20]), c_0_21]), c_0_22])])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (k1_funct_1(esk10_0,esk4_3(esk10_0,k1_relat_1(esk9_0),esk8_1(esk9_0)))=esk8_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_44]), c_0_19]), c_0_21])])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (k1_funct_1(esk9_0,esk8_1(esk9_0))=k1_funct_1(esk9_0,esk7_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_20]), c_0_22])])).
% 0.13/0.38  cnf(c_0_69, plain, (r2_hidden(esk7_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (X1=esk4_3(esk10_0,k1_relat_1(esk9_0),esk8_1(esk9_0))|k1_funct_1(k5_relat_1(esk10_0,esk9_0),X1)!=k1_funct_1(k5_relat_1(esk10_0,esk9_0),esk4_3(esk10_0,k1_relat_1(esk9_0),esk8_1(esk9_0)))|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (k1_funct_1(k5_relat_1(esk10_0,esk9_0),esk4_3(esk10_0,k1_relat_1(esk9_0),esk8_1(esk9_0)))=k1_funct_1(esk9_0,esk7_1(esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_65]), c_0_67]), c_0_68])).
% 0.13/0.38  cnf(c_0_72, negated_conjecture, (r2_hidden(k4_tarski(esk4_3(esk10_0,k1_relat_1(esk9_0),esk7_1(esk9_0)),esk7_1(esk9_0)),esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_69]), c_0_20]), c_0_22])]), c_0_39])).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, (X1=esk4_3(esk10_0,k1_relat_1(esk9_0),esk8_1(esk9_0))|k1_funct_1(k5_relat_1(esk10_0,esk9_0),X1)!=k1_funct_1(esk9_0,esk7_1(esk9_0))|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 0.13/0.38  cnf(c_0_74, negated_conjecture, (r2_hidden(esk4_3(esk10_0,k1_relat_1(esk9_0),esk7_1(esk9_0)),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_60, c_0_72])).
% 0.13/0.38  cnf(c_0_75, negated_conjecture, (k1_funct_1(esk10_0,esk4_3(esk10_0,k1_relat_1(esk9_0),esk7_1(esk9_0)))=esk7_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_72]), c_0_19]), c_0_21])])).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, (esk4_3(esk10_0,k1_relat_1(esk9_0),esk8_1(esk9_0))=esk4_3(esk10_0,k1_relat_1(esk9_0),esk7_1(esk9_0))|k1_funct_1(k5_relat_1(esk10_0,esk9_0),esk4_3(esk10_0,k1_relat_1(esk9_0),esk7_1(esk9_0)))!=k1_funct_1(esk9_0,esk7_1(esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.13/0.38  cnf(c_0_77, negated_conjecture, (k1_funct_1(k5_relat_1(esk10_0,esk9_0),esk4_3(esk10_0,k1_relat_1(esk9_0),esk7_1(esk9_0)))=k1_funct_1(esk9_0,esk7_1(esk9_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_74]), c_0_75])).
% 0.13/0.38  cnf(c_0_78, negated_conjecture, (esk4_3(esk10_0,k1_relat_1(esk9_0),esk8_1(esk9_0))=esk4_3(esk10_0,k1_relat_1(esk9_0),esk7_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77])])).
% 0.13/0.38  cnf(c_0_79, plain, (v2_funct_1(X1)|esk7_1(X1)!=esk8_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_80, negated_conjecture, (esk8_1(esk9_0)=esk7_1(esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_78]), c_0_75])).
% 0.13/0.38  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_20]), c_0_22])]), c_0_39]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 82
% 0.13/0.38  # Proof object clause steps            : 57
% 0.13/0.38  # Proof object formula steps           : 25
% 0.13/0.38  # Proof object conjectures             : 38
% 0.13/0.38  # Proof object clause conjectures      : 35
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 24
% 0.13/0.38  # Proof object initial formulas used   : 12
% 0.13/0.38  # Proof object generating inferences   : 23
% 0.13/0.38  # Proof object simplifying inferences  : 72
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 12
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 33
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 33
% 0.13/0.38  # Processed clauses                    : 104
% 0.13/0.38  # ...of these trivial                  : 3
% 0.13/0.38  # ...subsumed                          : 3
% 0.13/0.38  # ...remaining for further processing  : 98
% 0.13/0.38  # Other redundant clauses eliminated   : 7
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 10
% 0.13/0.38  # Backward-rewritten                   : 22
% 0.13/0.38  # Generated clauses                    : 184
% 0.13/0.38  # ...of the previous two non-trivial   : 158
% 0.13/0.38  # Contextual simplify-reflections      : 6
% 0.13/0.38  # Paramodulations                      : 177
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 7
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 59
% 0.13/0.38  #    Positive orientable unit clauses  : 19
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 39
% 0.13/0.38  # Current number of unprocessed clauses: 87
% 0.13/0.38  # ...number of literals in the above   : 364
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 32
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 856
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 197
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 17
% 0.13/0.38  # Unit Clause-clause subsumption calls : 44
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 20
% 0.13/0.38  # BW rewrite match successes           : 9
% 0.13/0.38  # Condensation attempts                : 104
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 8974
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.035 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.042 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
