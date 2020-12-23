%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:34 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 633 expanded)
%              Number of clauses        :   50 ( 297 expanded)
%              Number of leaves         :   10 ( 160 expanded)
%              Depth                    :   14
%              Number of atoms          :  253 (2182 expanded)
%              Number of equality atoms :   40 ( 508 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t34_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(t14_ordinal1,axiom,(
    ! [X1] : X1 != k1_ordinal1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(t41_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v4_ordinal1(X1)
      <=> ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X2,X1)
             => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

fof(t42_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( ~ ( ~ v4_ordinal1(X1)
            & ! [X2] :
                ( v3_ordinal1(X2)
               => X1 != k1_ordinal1(X2) ) )
        & ~ ( ? [X2] :
                ( v3_ordinal1(X2)
                & X1 = k1_ordinal1(X2) )
            & v4_ordinal1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_ordinal1)).

fof(t33_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(c_0_10,plain,(
    ! [X3,X4] :
      ( ( r1_tarski(X3,X4)
        | X3 != X4 )
      & ( r1_tarski(X4,X3)
        | X3 != X4 )
      & ( ~ r1_tarski(X3,X4)
        | ~ r1_tarski(X4,X3)
        | X3 = X4 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_11,plain,(
    ! [X8,X9] :
      ( ( ~ r1_ordinal1(X8,X9)
        | r1_tarski(X8,X9)
        | ~ v3_ordinal1(X8)
        | ~ v3_ordinal1(X9) )
      & ( ~ r1_tarski(X8,X9)
        | r1_ordinal1(X8,X9)
        | ~ v3_ordinal1(X8)
        | ~ v3_ordinal1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

fof(c_0_12,plain,(
    ! [X16,X17] :
      ( ( ~ r2_hidden(X16,k1_ordinal1(X17))
        | r1_ordinal1(X16,X17)
        | ~ v3_ordinal1(X17)
        | ~ v3_ordinal1(X16) )
      & ( ~ r1_ordinal1(X16,X17)
        | r2_hidden(X16,k1_ordinal1(X17))
        | ~ v3_ordinal1(X17)
        | ~ v3_ordinal1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).

fof(c_0_13,plain,(
    ! [X7] : k1_ordinal1(X7) = k2_xboole_0(X7,k1_tarski(X7)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_14,plain,(
    ! [X10,X11] :
      ( ( ~ r2_hidden(X10,k1_ordinal1(X11))
        | r2_hidden(X10,X11)
        | X10 = X11 )
      & ( ~ r2_hidden(X10,X11)
        | r2_hidden(X10,k1_ordinal1(X11)) )
      & ( X10 != X11
        | r2_hidden(X10,k1_ordinal1(X11)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_15,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r2_hidden(X1,k1_ordinal1(X2))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r1_ordinal1(X2,X1)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_24,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_26,plain,(
    ! [X12] : X12 != k1_ordinal1(X12) ),
    inference(variable_rename,[status(thm)],[t14_ordinal1])).

fof(c_0_27,plain,(
    ! [X13] :
      ( ~ v3_ordinal1(X13)
      | v3_ordinal1(k1_ordinal1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ r2_hidden(X2,X1)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | X1 != X2 ),
    inference(rw,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_30,plain,
    ( X1 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X18,X19] :
      ( ( ~ v4_ordinal1(X18)
        | ~ v3_ordinal1(X19)
        | ~ r2_hidden(X19,X18)
        | r2_hidden(k1_ordinal1(X19),X18)
        | ~ v3_ordinal1(X18) )
      & ( v3_ordinal1(esk1_1(X18))
        | v4_ordinal1(X18)
        | ~ v3_ordinal1(X18) )
      & ( r2_hidden(esk1_1(X18),X18)
        | v4_ordinal1(X18)
        | ~ v3_ordinal1(X18) )
      & ( ~ r2_hidden(k1_ordinal1(esk1_1(X18)),X18)
        | v4_ordinal1(X18)
        | ~ v3_ordinal1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_ordinal1])])])])])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_24])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( X1 != k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_18])).

cnf(c_0_36,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_31,c_0_18])).

cnf(c_0_37,plain,
    ( r2_hidden(k1_ordinal1(X2),X1)
    | ~ v4_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ( ~ ( ~ v4_ordinal1(X1)
              & ! [X2] :
                  ( v3_ordinal1(X2)
                 => X1 != k1_ordinal1(X2) ) )
          & ~ ( ? [X2] :
                  ( v3_ordinal1(X2)
                  & X1 = k1_ordinal1(X2) )
              & v4_ordinal1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t42_ordinal1])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_40,plain,
    ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ v4_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_37,c_0_18])).

fof(c_0_41,negated_conjecture,(
    ! [X22] :
      ( v3_ordinal1(esk2_0)
      & ( v3_ordinal1(esk3_0)
        | ~ v4_ordinal1(esk2_0) )
      & ( esk2_0 = k1_ordinal1(esk3_0)
        | ~ v4_ordinal1(esk2_0) )
      & ( v4_ordinal1(esk2_0)
        | ~ v4_ordinal1(esk2_0) )
      & ( v3_ordinal1(esk3_0)
        | ~ v3_ordinal1(X22)
        | esk2_0 != k1_ordinal1(X22) )
      & ( esk2_0 = k1_ordinal1(esk3_0)
        | ~ v3_ordinal1(X22)
        | esk2_0 != k1_ordinal1(X22) )
      & ( v4_ordinal1(esk2_0)
        | ~ v3_ordinal1(X22)
        | esk2_0 != k1_ordinal1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_38])])])])])])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_44,plain,(
    ! [X14,X15] :
      ( ( ~ r2_hidden(X14,X15)
        | r1_ordinal1(k1_ordinal1(X14),X15)
        | ~ v3_ordinal1(X15)
        | ~ v3_ordinal1(X14) )
      & ( ~ r1_ordinal1(k1_ordinal1(X14),X15)
        | r2_hidden(X14,X15)
        | ~ v3_ordinal1(X15)
        | ~ v3_ordinal1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).

cnf(c_0_45,plain,
    ( ~ v4_ordinal1(X1)
    | ~ r2_hidden(X1,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( esk2_0 = k1_ordinal1(esk3_0)
    | ~ v4_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_18])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r1_ordinal1(X1,X2) ),
    inference(rw,[status(thm)],[c_0_43,c_0_18])).

cnf(c_0_49,plain,
    ( r1_ordinal1(k1_ordinal1(X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( ~ v4_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_40]),c_0_34])]),c_0_36])).

cnf(c_0_53,negated_conjecture,
    ( esk2_0 = k2_xboole_0(esk3_0,k1_tarski(esk3_0))
    | ~ v4_ordinal1(esk2_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_18])).

cnf(c_0_54,negated_conjecture,
    ( v3_ordinal1(esk3_0)
    | ~ v4_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,plain,
    ( v3_ordinal1(esk1_1(X1))
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_56,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,plain,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_49,c_0_18])).

cnf(c_0_58,negated_conjecture,
    ( v4_ordinal1(esk2_0)
    | r2_hidden(esk1_1(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( ~ v4_ordinal1(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( v4_ordinal1(esk2_0)
    | v3_ordinal1(esk1_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_51])).

cnf(c_0_61,plain,
    ( v4_ordinal1(X1)
    | ~ r2_hidden(k1_ordinal1(esk1_1(X1)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,k1_tarski(X1)) = X2
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_36])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk1_1(esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( v3_ordinal1(esk1_1(esk2_0)) ),
    inference(sr,[status(thm)],[c_0_60,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( v4_ordinal1(esk2_0)
    | ~ v3_ordinal1(X1)
    | esk2_0 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_66,plain,
    ( v4_ordinal1(X1)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(k2_xboole_0(esk1_1(X1),k1_tarski(esk1_1(X1))),X1) ),
    inference(rw,[status(thm)],[c_0_61,c_0_18])).

cnf(c_0_67,negated_conjecture,
    ( k2_xboole_0(esk1_1(esk2_0),k1_tarski(esk1_1(esk2_0))) = esk2_0
    | r2_hidden(k2_xboole_0(esk1_1(esk2_0),k1_tarski(esk1_1(esk2_0))),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_51]),c_0_64])])).

cnf(c_0_68,negated_conjecture,
    ( v4_ordinal1(esk2_0)
    | esk2_0 != k2_xboole_0(X1,k1_tarski(X1))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_65,c_0_18])).

cnf(c_0_69,negated_conjecture,
    ( k2_xboole_0(esk1_1(esk2_0),k1_tarski(esk1_1(esk2_0))) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_51])]),c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_64])]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.029 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.43  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.19/0.43  fof(t34_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 0.19/0.43  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.19/0.43  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.19/0.43  fof(t14_ordinal1, axiom, ![X1]:X1!=k1_ordinal1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_ordinal1)).
% 0.19/0.43  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.19/0.43  fof(t41_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_ordinal1)).
% 0.19/0.43  fof(t42_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(~((~(v4_ordinal1(X1))&![X2]:(v3_ordinal1(X2)=>X1!=k1_ordinal1(X2))))&~((?[X2]:(v3_ordinal1(X2)&X1=k1_ordinal1(X2))&v4_ordinal1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_ordinal1)).
% 0.19/0.43  fof(t33_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 0.19/0.43  fof(c_0_10, plain, ![X3, X4]:(((r1_tarski(X3,X4)|X3!=X4)&(r1_tarski(X4,X3)|X3!=X4))&(~r1_tarski(X3,X4)|~r1_tarski(X4,X3)|X3=X4)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.43  fof(c_0_11, plain, ![X8, X9]:((~r1_ordinal1(X8,X9)|r1_tarski(X8,X9)|(~v3_ordinal1(X8)|~v3_ordinal1(X9)))&(~r1_tarski(X8,X9)|r1_ordinal1(X8,X9)|(~v3_ordinal1(X8)|~v3_ordinal1(X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.19/0.43  fof(c_0_12, plain, ![X16, X17]:((~r2_hidden(X16,k1_ordinal1(X17))|r1_ordinal1(X16,X17)|~v3_ordinal1(X17)|~v3_ordinal1(X16))&(~r1_ordinal1(X16,X17)|r2_hidden(X16,k1_ordinal1(X17))|~v3_ordinal1(X17)|~v3_ordinal1(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).
% 0.19/0.43  fof(c_0_13, plain, ![X7]:k1_ordinal1(X7)=k2_xboole_0(X7,k1_tarski(X7)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.19/0.43  fof(c_0_14, plain, ![X10, X11]:((~r2_hidden(X10,k1_ordinal1(X11))|(r2_hidden(X10,X11)|X10=X11))&((~r2_hidden(X10,X11)|r2_hidden(X10,k1_ordinal1(X11)))&(X10!=X11|r2_hidden(X10,k1_ordinal1(X11))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.19/0.43  cnf(c_0_15, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.43  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.43  cnf(c_0_17, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,k1_ordinal1(X2))|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  cnf(c_0_18, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.43  cnf(c_0_19, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.43  cnf(c_0_20, plain, (X1=X2|~r1_ordinal1(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.43  cnf(c_0_21, plain, (r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.43  cnf(c_0_22, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.19/0.43  cnf(c_0_23, plain, (X1=X2|~r1_ordinal1(X2,X1)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(spm,[status(thm)],[c_0_20, c_0_16])).
% 0.19/0.43  cnf(c_0_24, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.43  cnf(c_0_25, plain, (r2_hidden(X1,k1_ordinal1(X2))|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.43  fof(c_0_26, plain, ![X12]:X12!=k1_ordinal1(X12), inference(variable_rename,[status(thm)],[t14_ordinal1])).
% 0.19/0.43  fof(c_0_27, plain, ![X13]:(~v3_ordinal1(X13)|v3_ordinal1(k1_ordinal1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.19/0.43  cnf(c_0_28, plain, (X1=X2|~r2_hidden(X2,X1)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.43  cnf(c_0_29, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|X1!=X2), inference(rw,[status(thm)],[c_0_25, c_0_18])).
% 0.19/0.43  cnf(c_0_30, plain, (X1!=k1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.43  cnf(c_0_31, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.43  fof(c_0_32, plain, ![X18, X19]:((~v4_ordinal1(X18)|(~v3_ordinal1(X19)|(~r2_hidden(X19,X18)|r2_hidden(k1_ordinal1(X19),X18)))|~v3_ordinal1(X18))&((v3_ordinal1(esk1_1(X18))|v4_ordinal1(X18)|~v3_ordinal1(X18))&((r2_hidden(esk1_1(X18),X18)|v4_ordinal1(X18)|~v3_ordinal1(X18))&(~r2_hidden(k1_ordinal1(esk1_1(X18)),X18)|v4_ordinal1(X18)|~v3_ordinal1(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_ordinal1])])])])])).
% 0.19/0.43  cnf(c_0_33, plain, (X1=X2|~r2_hidden(X2,X1)|~r2_hidden(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(spm,[status(thm)],[c_0_28, c_0_24])).
% 0.19/0.43  cnf(c_0_34, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(er,[status(thm)],[c_0_29])).
% 0.19/0.43  cnf(c_0_35, plain, (X1!=k2_xboole_0(X1,k1_tarski(X1))), inference(rw,[status(thm)],[c_0_30, c_0_18])).
% 0.19/0.43  cnf(c_0_36, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_31, c_0_18])).
% 0.19/0.43  cnf(c_0_37, plain, (r2_hidden(k1_ordinal1(X2),X1)|~v4_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X2,X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.43  fof(c_0_38, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(~((~(v4_ordinal1(X1))&![X2]:(v3_ordinal1(X2)=>X1!=k1_ordinal1(X2))))&~((?[X2]:(v3_ordinal1(X2)&X1=k1_ordinal1(X2))&v4_ordinal1(X1)))))), inference(assume_negation,[status(cth)],[t42_ordinal1])).
% 0.19/0.43  cnf(c_0_39, plain, (~r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X1)|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])).
% 0.19/0.43  cnf(c_0_40, plain, (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X1)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~v4_ordinal1(X1)|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_37, c_0_18])).
% 0.19/0.43  fof(c_0_41, negated_conjecture, ![X22]:(v3_ordinal1(esk2_0)&((((v3_ordinal1(esk3_0)|~v4_ordinal1(esk2_0))&(esk2_0=k1_ordinal1(esk3_0)|~v4_ordinal1(esk2_0)))&(v4_ordinal1(esk2_0)|~v4_ordinal1(esk2_0)))&(((v3_ordinal1(esk3_0)|(~v3_ordinal1(X22)|esk2_0!=k1_ordinal1(X22)))&(esk2_0=k1_ordinal1(esk3_0)|(~v3_ordinal1(X22)|esk2_0!=k1_ordinal1(X22))))&(v4_ordinal1(esk2_0)|(~v3_ordinal1(X22)|esk2_0!=k1_ordinal1(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_38])])])])])])).
% 0.19/0.43  cnf(c_0_42, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.43  cnf(c_0_43, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  fof(c_0_44, plain, ![X14, X15]:((~r2_hidden(X14,X15)|r1_ordinal1(k1_ordinal1(X14),X15)|~v3_ordinal1(X15)|~v3_ordinal1(X14))&(~r1_ordinal1(k1_ordinal1(X14),X15)|r2_hidden(X14,X15)|~v3_ordinal1(X15)|~v3_ordinal1(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).
% 0.19/0.43  cnf(c_0_45, plain, (~v4_ordinal1(X1)|~r2_hidden(X1,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.43  cnf(c_0_46, negated_conjecture, (esk2_0=k1_ordinal1(esk3_0)|~v4_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.43  cnf(c_0_47, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_42, c_0_18])).
% 0.19/0.43  cnf(c_0_48, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r1_ordinal1(X1,X2)), inference(rw,[status(thm)],[c_0_43, c_0_18])).
% 0.19/0.43  cnf(c_0_49, plain, (r1_ordinal1(k1_ordinal1(X1),X2)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.43  cnf(c_0_50, plain, (r2_hidden(esk1_1(X1),X1)|v4_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.43  cnf(c_0_51, negated_conjecture, (v3_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.43  cnf(c_0_52, plain, (~v4_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_40]), c_0_34])]), c_0_36])).
% 0.19/0.43  cnf(c_0_53, negated_conjecture, (esk2_0=k2_xboole_0(esk3_0,k1_tarski(esk3_0))|~v4_ordinal1(esk2_0)), inference(rw,[status(thm)],[c_0_46, c_0_18])).
% 0.19/0.43  cnf(c_0_54, negated_conjecture, (v3_ordinal1(esk3_0)|~v4_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.43  cnf(c_0_55, plain, (v3_ordinal1(esk1_1(X1))|v4_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.43  cnf(c_0_56, plain, (X1=X2|r2_hidden(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.43  cnf(c_0_57, plain, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_49, c_0_18])).
% 0.19/0.43  cnf(c_0_58, negated_conjecture, (v4_ordinal1(esk2_0)|r2_hidden(esk1_1(esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.43  cnf(c_0_59, negated_conjecture, (~v4_ordinal1(esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.19/0.43  cnf(c_0_60, negated_conjecture, (v4_ordinal1(esk2_0)|v3_ordinal1(esk1_1(esk2_0))), inference(spm,[status(thm)],[c_0_55, c_0_51])).
% 0.19/0.43  cnf(c_0_61, plain, (v4_ordinal1(X1)|~r2_hidden(k1_ordinal1(esk1_1(X1)),X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.43  cnf(c_0_62, plain, (k2_xboole_0(X1,k1_tarski(X1))=X2|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X2)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_36])).
% 0.19/0.43  cnf(c_0_63, negated_conjecture, (r2_hidden(esk1_1(esk2_0),esk2_0)), inference(sr,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.43  cnf(c_0_64, negated_conjecture, (v3_ordinal1(esk1_1(esk2_0))), inference(sr,[status(thm)],[c_0_60, c_0_59])).
% 0.19/0.43  cnf(c_0_65, negated_conjecture, (v4_ordinal1(esk2_0)|~v3_ordinal1(X1)|esk2_0!=k1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.43  cnf(c_0_66, plain, (v4_ordinal1(X1)|~v3_ordinal1(X1)|~r2_hidden(k2_xboole_0(esk1_1(X1),k1_tarski(esk1_1(X1))),X1)), inference(rw,[status(thm)],[c_0_61, c_0_18])).
% 0.19/0.43  cnf(c_0_67, negated_conjecture, (k2_xboole_0(esk1_1(esk2_0),k1_tarski(esk1_1(esk2_0)))=esk2_0|r2_hidden(k2_xboole_0(esk1_1(esk2_0),k1_tarski(esk1_1(esk2_0))),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_51]), c_0_64])])).
% 0.19/0.43  cnf(c_0_68, negated_conjecture, (v4_ordinal1(esk2_0)|esk2_0!=k2_xboole_0(X1,k1_tarski(X1))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_65, c_0_18])).
% 0.19/0.43  cnf(c_0_69, negated_conjecture, (k2_xboole_0(esk1_1(esk2_0),k1_tarski(esk1_1(esk2_0)))=esk2_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_51])]), c_0_59])).
% 0.19/0.43  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_64])]), c_0_59]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 71
% 0.19/0.43  # Proof object clause steps            : 50
% 0.19/0.43  # Proof object formula steps           : 21
% 0.19/0.43  # Proof object conjectures             : 17
% 0.19/0.43  # Proof object clause conjectures      : 14
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 19
% 0.19/0.43  # Proof object initial formulas used   : 10
% 0.19/0.43  # Proof object generating inferences   : 16
% 0.19/0.43  # Proof object simplifying inferences  : 31
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 11
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 27
% 0.19/0.43  # Removed in clause preprocessing      : 2
% 0.19/0.43  # Initial clauses in saturation        : 25
% 0.19/0.43  # Processed clauses                    : 684
% 0.19/0.43  # ...of these trivial                  : 0
% 0.19/0.43  # ...subsumed                          : 403
% 0.19/0.43  # ...remaining for further processing  : 281
% 0.19/0.43  # Other redundant clauses eliminated   : 3
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 31
% 0.19/0.43  # Backward-rewritten                   : 19
% 0.19/0.43  # Generated clauses                    : 1535
% 0.19/0.43  # ...of the previous two non-trivial   : 1360
% 0.19/0.43  # Contextual simplify-reflections      : 49
% 0.19/0.43  # Paramodulations                      : 1527
% 0.19/0.43  # Factorizations                       : 0
% 0.19/0.43  # Equation resolutions                 : 3
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 199
% 0.19/0.43  #    Positive orientable unit clauses  : 13
% 0.19/0.43  #    Positive unorientable unit clauses: 0
% 0.19/0.43  #    Negative unit clauses             : 7
% 0.19/0.43  #    Non-unit-clauses                  : 179
% 0.19/0.43  # Current number of unprocessed clauses: 514
% 0.19/0.43  # ...number of literals in the above   : 2420
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 80
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 5868
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 2368
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 207
% 0.19/0.43  # Unit Clause-clause subsumption calls : 191
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 6
% 0.19/0.43  # BW rewrite match successes           : 6
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 46721
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.084 s
% 0.19/0.43  # System time              : 0.005 s
% 0.19/0.43  # Total time               : 0.089 s
% 0.19/0.43  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
