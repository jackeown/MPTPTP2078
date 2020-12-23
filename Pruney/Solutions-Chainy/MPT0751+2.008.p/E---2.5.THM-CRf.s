%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 (1903 expanded)
%              Number of clauses        :   70 ( 853 expanded)
%              Number of leaves         :   10 ( 474 expanded)
%              Depth                    :   17
%              Number of atoms          :  313 (7463 expanded)
%              Number of equality atoms :   41 (1841 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v4_ordinal1(X1)
      <=> ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X2,X1)
             => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

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

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(t34_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(t33_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(t14_ordinal1,axiom,(
    ! [X1] : X1 != k1_ordinal1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

fof(fc2_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( ~ v1_xboole_0(k1_ordinal1(X1))
        & v3_ordinal1(k1_ordinal1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_ordinal1)).

fof(c_0_10,plain,(
    ! [X18,X19] :
      ( ( ~ v4_ordinal1(X18)
        | ~ v3_ordinal1(X19)
        | ~ r2_hidden(X19,X18)
        | r2_hidden(k1_ordinal1(X19),X18)
        | ~ v3_ordinal1(X18) )
      & ( v3_ordinal1(esk2_1(X18))
        | v4_ordinal1(X18)
        | ~ v3_ordinal1(X18) )
      & ( r2_hidden(esk2_1(X18),X18)
        | v4_ordinal1(X18)
        | ~ v3_ordinal1(X18) )
      & ( ~ r2_hidden(k1_ordinal1(esk2_1(X18)),X18)
        | v4_ordinal1(X18)
        | ~ v3_ordinal1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_ordinal1])])])])])).

fof(c_0_11,plain,(
    ! [X7] : k1_ordinal1(X7) = k2_xboole_0(X7,k1_tarski(X7)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

cnf(c_0_12,plain,
    ( r2_hidden(k1_ordinal1(X2),X1)
    | ~ v4_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X12,X13] :
      ( ~ v3_ordinal1(X13)
      | ~ r2_hidden(X12,X13)
      | v3_ordinal1(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X9,X10] :
      ( ( ~ r2_hidden(X9,k1_ordinal1(X10))
        | r2_hidden(X9,X10)
        | X9 = X10 )
      & ( ~ r2_hidden(X9,X10)
        | r2_hidden(X9,k1_ordinal1(X10)) )
      & ( X9 != X10
        | r2_hidden(X9,k1_ordinal1(X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_17,plain,
    ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ v4_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
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

fof(c_0_20,negated_conjecture,(
    ! [X22] :
      ( v3_ordinal1(esk3_0)
      & ( v3_ordinal1(esk4_0)
        | ~ v4_ordinal1(esk3_0) )
      & ( esk3_0 = k1_ordinal1(esk4_0)
        | ~ v4_ordinal1(esk3_0) )
      & ( v4_ordinal1(esk3_0)
        | ~ v4_ordinal1(esk3_0) )
      & ( v3_ordinal1(esk4_0)
        | ~ v3_ordinal1(X22)
        | esk3_0 != k1_ordinal1(X22) )
      & ( esk3_0 = k1_ordinal1(esk4_0)
        | ~ v3_ordinal1(X22)
        | esk3_0 != k1_ordinal1(X22) )
      & ( v4_ordinal1(esk3_0)
        | ~ v3_ordinal1(X22)
        | esk3_0 != k1_ordinal1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
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

cnf(c_0_23,plain,
    ( r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v4_ordinal1(X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r2_hidden(X1,k1_ordinal1(X2))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( esk3_0 = k1_ordinal1(esk4_0)
    | ~ v4_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | X1 != X2 ),
    inference(rw,[status(thm)],[c_0_21,c_0_13])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( r1_ordinal1(k1_ordinal1(X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v4_ordinal1(X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_23])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_13])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_ordinal1(k1_ordinal1(X1),X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( esk3_0 = k2_xboole_0(esk4_0,k1_tarski(esk4_0))
    | ~ v4_ordinal1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( v3_ordinal1(esk4_0)
    | ~ v4_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r1_ordinal1(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_13])).

cnf(c_0_38,plain,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_13])).

cnf(c_0_39,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v4_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))
    | ~ v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( r1_ordinal1(X1,esk4_0)
    | ~ v4_ordinal1(esk3_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_43,plain,
    ( v3_ordinal1(X1)
    | ~ v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ v4_ordinal1(esk3_0)
    | ~ r1_ordinal1(X1,esk4_0)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_34]),c_0_35])).

cnf(c_0_45,plain,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_38,c_0_18])).

cnf(c_0_46,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v4_ordinal1(esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_34]),c_0_40])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ v4_ordinal1(esk3_0)
    | ~ v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_35])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_49,plain,(
    ! [X4,X5] :
      ( ( ~ r2_hidden(esk1_2(X4,X5),X4)
        | ~ r2_hidden(esk1_2(X4,X5),X5)
        | X4 = X5 )
      & ( r2_hidden(esk1_2(X4,X5),X4)
        | r2_hidden(esk1_2(X4,X5),X5)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_50,plain,(
    ! [X11] : X11 != k1_ordinal1(X11) ),
    inference(variable_rename,[status(thm)],[t14_ordinal1])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk3_0)
    | ~ v4_ordinal1(esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_35]),c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ v4_ordinal1(esk3_0)
    | ~ v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_23]),c_0_40])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | ~ v4_ordinal1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_54,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_48,c_0_13])).

cnf(c_0_55,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( X1 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_31]),c_0_18])).

cnf(c_0_58,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(k2_xboole_0(X1,k1_tarski(X1)),k1_tarski(k2_xboole_0(X1,k1_tarski(X1)))))
    | ~ v4_ordinal1(esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_51]),c_0_40])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk4_0,esk4_0)
    | ~ v4_ordinal1(esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_34]),c_0_40])]),c_0_53])).

cnf(c_0_60,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,plain,
    ( esk1_2(X1,k2_xboole_0(X2,k1_tarski(X2))) = X2
    | X1 = k2_xboole_0(X2,k1_tarski(X2))
    | r2_hidden(esk1_2(X1,k2_xboole_0(X2,k1_tarski(X2))),X1)
    | r2_hidden(esk1_2(X1,k2_xboole_0(X2,k1_tarski(X2))),X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,plain,
    ( X1 != k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_13])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_57])).

cnf(c_0_64,plain,
    ( v3_ordinal1(X1)
    | ~ v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_31])).

cnf(c_0_65,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))
    | ~ v4_ordinal1(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_34]),c_0_59])).

cnf(c_0_66,plain,
    ( X1 = k2_xboole_0(X2,k1_tarski(X2))
    | ~ r2_hidden(esk1_2(X1,k2_xboole_0(X2,k1_tarski(X2))),X1)
    | ~ r2_hidden(esk1_2(X1,k2_xboole_0(X2,k1_tarski(X2))),X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_31])).

cnf(c_0_67,plain,
    ( esk1_2(X1,k2_xboole_0(X1,k1_tarski(X1))) = X1
    | r2_hidden(esk1_2(X1,k2_xboole_0(X1,k1_tarski(X1))),X1) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_61]),c_0_62])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))
    | ~ v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_37]),c_0_43]),c_0_43])).

cnf(c_0_69,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ v4_ordinal1(esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_70,plain,
    ( v4_ordinal1(X1)
    | ~ r2_hidden(k1_ordinal1(esk2_1(X1)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_71,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_37])).

fof(c_0_72,plain,(
    ! [X8] :
      ( ( ~ v1_xboole_0(k1_ordinal1(X8))
        | ~ v3_ordinal1(X8) )
      & ( v3_ordinal1(k1_ordinal1(X8))
        | ~ v3_ordinal1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_ordinal1])])])])).

cnf(c_0_73,plain,
    ( esk1_2(X1,k2_xboole_0(X1,k1_tarski(X1))) = X1 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_62]),c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk4_0,k1_tarski(esk4_0)))
    | ~ v4_ordinal1(esk3_0)
    | ~ v3_ordinal1(k2_xboole_0(esk4_0,k1_tarski(esk4_0)))
    | ~ r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_42]),c_0_69])).

cnf(c_0_75,plain,
    ( v4_ordinal1(X1)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(k2_xboole_0(esk2_1(X1),k1_tarski(esk2_1(X1))),X1) ),
    inference(rw,[status(thm)],[c_0_70,c_0_13])).

cnf(c_0_76,plain,
    ( k2_xboole_0(X1,k1_tarski(X1)) = X2
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_45])).

cnf(c_0_77,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_78,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_79,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_73]),c_0_36])]),c_0_62])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk4_0,k1_tarski(esk4_0)))
    | ~ v4_ordinal1(esk3_0)
    | ~ v3_ordinal1(k2_xboole_0(esk4_0,k1_tarski(esk4_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_23]),c_0_40])])).

cnf(c_0_81,negated_conjecture,
    ( v4_ordinal1(esk3_0)
    | ~ v3_ordinal1(X1)
    | esk3_0 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_82,plain,
    ( k2_xboole_0(esk2_1(X1),k1_tarski(esk2_1(X1))) = X1
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(k2_xboole_0(esk2_1(X1),k1_tarski(esk2_1(X1))))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_83,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_78,c_0_13])).

cnf(c_0_84,plain,
    ( v3_ordinal1(esk2_1(X1))
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_85,negated_conjecture,
    ( ~ v4_ordinal1(esk3_0)
    | ~ r2_hidden(k2_xboole_0(esk4_0,k1_tarski(esk4_0)),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_69])).

cnf(c_0_86,negated_conjecture,
    ( v4_ordinal1(esk3_0)
    | esk3_0 != k2_xboole_0(X1,k1_tarski(X1))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_81,c_0_13])).

cnf(c_0_87,plain,
    ( k2_xboole_0(esk2_1(X1),k1_tarski(esk2_1(X1))) = X1
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( ~ v4_ordinal1(esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_23]),c_0_40])]),c_0_53])).

cnf(c_0_89,negated_conjecture,
    ( ~ v3_ordinal1(esk2_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])]),c_0_40])]),c_0_88])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_84]),c_0_40])]),c_0_88]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:24:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.42  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.028 s
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t41_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_ordinal1)).
% 0.20/0.42  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.20/0.42  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.20/0.42  fof(t42_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(~((~(v4_ordinal1(X1))&![X2]:(v3_ordinal1(X2)=>X1!=k1_ordinal1(X2))))&~((?[X2]:(v3_ordinal1(X2)&X1=k1_ordinal1(X2))&v4_ordinal1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_ordinal1)).
% 0.20/0.42  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.20/0.42  fof(t34_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 0.20/0.42  fof(t33_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 0.20/0.42  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 0.20/0.42  fof(t14_ordinal1, axiom, ![X1]:X1!=k1_ordinal1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_ordinal1)).
% 0.20/0.42  fof(fc2_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(~(v1_xboole_0(k1_ordinal1(X1)))&v3_ordinal1(k1_ordinal1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_ordinal1)).
% 0.20/0.42  fof(c_0_10, plain, ![X18, X19]:((~v4_ordinal1(X18)|(~v3_ordinal1(X19)|(~r2_hidden(X19,X18)|r2_hidden(k1_ordinal1(X19),X18)))|~v3_ordinal1(X18))&((v3_ordinal1(esk2_1(X18))|v4_ordinal1(X18)|~v3_ordinal1(X18))&((r2_hidden(esk2_1(X18),X18)|v4_ordinal1(X18)|~v3_ordinal1(X18))&(~r2_hidden(k1_ordinal1(esk2_1(X18)),X18)|v4_ordinal1(X18)|~v3_ordinal1(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_ordinal1])])])])])).
% 0.20/0.42  fof(c_0_11, plain, ![X7]:k1_ordinal1(X7)=k2_xboole_0(X7,k1_tarski(X7)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.20/0.42  cnf(c_0_12, plain, (r2_hidden(k1_ordinal1(X2),X1)|~v4_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X2,X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.42  cnf(c_0_13, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.42  fof(c_0_14, plain, ![X12, X13]:(~v3_ordinal1(X13)|(~r2_hidden(X12,X13)|v3_ordinal1(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.20/0.42  fof(c_0_15, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(~((~(v4_ordinal1(X1))&![X2]:(v3_ordinal1(X2)=>X1!=k1_ordinal1(X2))))&~((?[X2]:(v3_ordinal1(X2)&X1=k1_ordinal1(X2))&v4_ordinal1(X1)))))), inference(assume_negation,[status(cth)],[t42_ordinal1])).
% 0.20/0.42  fof(c_0_16, plain, ![X9, X10]:((~r2_hidden(X9,k1_ordinal1(X10))|(r2_hidden(X9,X10)|X9=X10))&((~r2_hidden(X9,X10)|r2_hidden(X9,k1_ordinal1(X10)))&(X9!=X10|r2_hidden(X9,k1_ordinal1(X10))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.20/0.42  cnf(c_0_17, plain, (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X1)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~v4_ordinal1(X1)|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.42  cnf(c_0_18, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  fof(c_0_19, plain, ![X16, X17]:((~r2_hidden(X16,k1_ordinal1(X17))|r1_ordinal1(X16,X17)|~v3_ordinal1(X17)|~v3_ordinal1(X16))&(~r1_ordinal1(X16,X17)|r2_hidden(X16,k1_ordinal1(X17))|~v3_ordinal1(X17)|~v3_ordinal1(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).
% 0.20/0.42  fof(c_0_20, negated_conjecture, ![X22]:(v3_ordinal1(esk3_0)&((((v3_ordinal1(esk4_0)|~v4_ordinal1(esk3_0))&(esk3_0=k1_ordinal1(esk4_0)|~v4_ordinal1(esk3_0)))&(v4_ordinal1(esk3_0)|~v4_ordinal1(esk3_0)))&(((v3_ordinal1(esk4_0)|(~v3_ordinal1(X22)|esk3_0!=k1_ordinal1(X22)))&(esk3_0=k1_ordinal1(esk4_0)|(~v3_ordinal1(X22)|esk3_0!=k1_ordinal1(X22))))&(v4_ordinal1(esk3_0)|(~v3_ordinal1(X22)|esk3_0!=k1_ordinal1(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).
% 0.20/0.42  cnf(c_0_21, plain, (r2_hidden(X1,k1_ordinal1(X2))|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  fof(c_0_22, plain, ![X14, X15]:((~r2_hidden(X14,X15)|r1_ordinal1(k1_ordinal1(X14),X15)|~v3_ordinal1(X15)|~v3_ordinal1(X14))&(~r1_ordinal1(k1_ordinal1(X14),X15)|r2_hidden(X14,X15)|~v3_ordinal1(X15)|~v3_ordinal1(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).
% 0.20/0.42  cnf(c_0_23, plain, (r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v4_ordinal1(X2)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.42  cnf(c_0_24, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_25, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,k1_ordinal1(X2))|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_26, negated_conjecture, (esk3_0=k1_ordinal1(esk4_0)|~v4_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  cnf(c_0_27, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|X1!=X2), inference(rw,[status(thm)],[c_0_21, c_0_13])).
% 0.20/0.42  cnf(c_0_28, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_29, plain, (r1_ordinal1(k1_ordinal1(X1),X2)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_30, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v4_ordinal1(X2)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_18, c_0_23])).
% 0.20/0.42  cnf(c_0_31, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_13])).
% 0.20/0.42  cnf(c_0_32, plain, (r2_hidden(X1,X2)|~r1_ordinal1(k1_ordinal1(X1),X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_33, plain, (r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_25, c_0_13])).
% 0.20/0.42  cnf(c_0_34, negated_conjecture, (esk3_0=k2_xboole_0(esk4_0,k1_tarski(esk4_0))|~v4_ordinal1(esk3_0)), inference(rw,[status(thm)],[c_0_26, c_0_13])).
% 0.20/0.42  cnf(c_0_35, negated_conjecture, (v3_ordinal1(esk4_0)|~v4_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  cnf(c_0_36, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(er,[status(thm)],[c_0_27])).
% 0.20/0.42  cnf(c_0_37, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r1_ordinal1(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_13])).
% 0.20/0.42  cnf(c_0_38, plain, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_13])).
% 0.20/0.42  cnf(c_0_39, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v4_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))|~v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.42  cnf(c_0_40, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  cnf(c_0_41, plain, (r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)), inference(rw,[status(thm)],[c_0_32, c_0_13])).
% 0.20/0.42  cnf(c_0_42, negated_conjecture, (r1_ordinal1(X1,esk4_0)|~v4_ordinal1(esk3_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.20/0.42  cnf(c_0_43, plain, (v3_ordinal1(X1)|~v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))), inference(spm,[status(thm)],[c_0_18, c_0_36])).
% 0.20/0.42  cnf(c_0_44, negated_conjecture, (r2_hidden(X1,esk3_0)|~v4_ordinal1(esk3_0)|~r1_ordinal1(X1,esk4_0)|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_34]), c_0_35])).
% 0.20/0.42  cnf(c_0_45, plain, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_38, c_0_18])).
% 0.20/0.42  cnf(c_0_46, negated_conjecture, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v4_ordinal1(esk3_0)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_34]), c_0_40])])).
% 0.20/0.42  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,esk4_0)|~v4_ordinal1(esk3_0)|~v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_35])).
% 0.20/0.42  cnf(c_0_48, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  fof(c_0_49, plain, ![X4, X5]:((~r2_hidden(esk1_2(X4,X5),X4)|~r2_hidden(esk1_2(X4,X5),X5)|X4=X5)&(r2_hidden(esk1_2(X4,X5),X4)|r2_hidden(esk1_2(X4,X5),X5)|X4=X5)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.20/0.42  fof(c_0_50, plain, ![X11]:X11!=k1_ordinal1(X11), inference(variable_rename,[status(thm)],[t14_ordinal1])).
% 0.20/0.42  cnf(c_0_51, negated_conjecture, (r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk3_0)|~v4_ordinal1(esk3_0)|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_35]), c_0_46])).
% 0.20/0.42  cnf(c_0_52, negated_conjecture, (r2_hidden(X1,esk4_0)|~v4_ordinal1(esk3_0)|~v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_23]), c_0_40])])).
% 0.20/0.42  cnf(c_0_53, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|~v4_ordinal1(esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_34])).
% 0.20/0.42  cnf(c_0_54, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_48, c_0_13])).
% 0.20/0.42  cnf(c_0_55, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.42  cnf(c_0_56, plain, (X1!=k1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.42  cnf(c_0_57, plain, (r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_31]), c_0_18])).
% 0.20/0.42  cnf(c_0_58, negated_conjecture, (v3_ordinal1(k2_xboole_0(k2_xboole_0(X1,k1_tarski(X1)),k1_tarski(k2_xboole_0(X1,k1_tarski(X1)))))|~v4_ordinal1(esk3_0)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_51]), c_0_40])])).
% 0.20/0.42  cnf(c_0_59, negated_conjecture, (r2_hidden(esk4_0,esk4_0)|~v4_ordinal1(esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_34]), c_0_40])]), c_0_53])).
% 0.20/0.42  cnf(c_0_60, plain, (X1=X2|~r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.42  cnf(c_0_61, plain, (esk1_2(X1,k2_xboole_0(X2,k1_tarski(X2)))=X2|X1=k2_xboole_0(X2,k1_tarski(X2))|r2_hidden(esk1_2(X1,k2_xboole_0(X2,k1_tarski(X2))),X1)|r2_hidden(esk1_2(X1,k2_xboole_0(X2,k1_tarski(X2))),X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.42  cnf(c_0_62, plain, (X1!=k2_xboole_0(X1,k1_tarski(X1))), inference(rw,[status(thm)],[c_0_56, c_0_13])).
% 0.20/0.42  cnf(c_0_63, plain, (r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X2)), inference(spm,[status(thm)],[c_0_41, c_0_57])).
% 0.20/0.42  cnf(c_0_64, plain, (v3_ordinal1(X1)|~v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_18, c_0_31])).
% 0.20/0.42  cnf(c_0_65, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))|~v4_ordinal1(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_34]), c_0_59])).
% 0.20/0.42  cnf(c_0_66, plain, (X1=k2_xboole_0(X2,k1_tarski(X2))|~r2_hidden(esk1_2(X1,k2_xboole_0(X2,k1_tarski(X2))),X1)|~r2_hidden(esk1_2(X1,k2_xboole_0(X2,k1_tarski(X2))),X2)), inference(spm,[status(thm)],[c_0_60, c_0_31])).
% 0.20/0.42  cnf(c_0_67, plain, (esk1_2(X1,k2_xboole_0(X1,k1_tarski(X1)))=X1|r2_hidden(esk1_2(X1,k2_xboole_0(X1,k1_tarski(X1))),X1)), inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_61]), c_0_62])).
% 0.20/0.42  cnf(c_0_68, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(k2_xboole_0(X2,k1_tarski(X2)))|~v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_37]), c_0_43]), c_0_43])).
% 0.20/0.42  cnf(c_0_69, negated_conjecture, (v3_ordinal1(X1)|~v4_ordinal1(esk3_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.42  cnf(c_0_70, plain, (v4_ordinal1(X1)|~r2_hidden(k1_ordinal1(esk2_1(X1)),X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.42  cnf(c_0_71, plain, (X1=X2|r2_hidden(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_54, c_0_37])).
% 0.20/0.42  fof(c_0_72, plain, ![X8]:((~v1_xboole_0(k1_ordinal1(X8))|~v3_ordinal1(X8))&(v3_ordinal1(k1_ordinal1(X8))|~v3_ordinal1(X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_ordinal1])])])])).
% 0.20/0.42  cnf(c_0_73, plain, (esk1_2(X1,k2_xboole_0(X1,k1_tarski(X1)))=X1), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_62]), c_0_67])).
% 0.20/0.42  cnf(c_0_74, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk4_0,k1_tarski(esk4_0)))|~v4_ordinal1(esk3_0)|~v3_ordinal1(k2_xboole_0(esk4_0,k1_tarski(esk4_0)))|~r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_42]), c_0_69])).
% 0.20/0.42  cnf(c_0_75, plain, (v4_ordinal1(X1)|~v3_ordinal1(X1)|~r2_hidden(k2_xboole_0(esk2_1(X1),k1_tarski(esk2_1(X1))),X1)), inference(rw,[status(thm)],[c_0_70, c_0_13])).
% 0.20/0.42  cnf(c_0_76, plain, (k2_xboole_0(X1,k1_tarski(X1))=X2|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_71, c_0_45])).
% 0.20/0.42  cnf(c_0_77, plain, (r2_hidden(esk2_1(X1),X1)|v4_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.42  cnf(c_0_78, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.42  cnf(c_0_79, plain, (~r2_hidden(X1,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_73]), c_0_36])]), c_0_62])).
% 0.20/0.42  cnf(c_0_80, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk4_0,k1_tarski(esk4_0)))|~v4_ordinal1(esk3_0)|~v3_ordinal1(k2_xboole_0(esk4_0,k1_tarski(esk4_0)))|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_23]), c_0_40])])).
% 0.20/0.42  cnf(c_0_81, negated_conjecture, (v4_ordinal1(esk3_0)|~v3_ordinal1(X1)|esk3_0!=k1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  cnf(c_0_82, plain, (k2_xboole_0(esk2_1(X1),k1_tarski(esk2_1(X1)))=X1|v4_ordinal1(X1)|~v3_ordinal1(k2_xboole_0(esk2_1(X1),k1_tarski(esk2_1(X1))))|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])).
% 0.20/0.42  cnf(c_0_83, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_78, c_0_13])).
% 0.20/0.42  cnf(c_0_84, plain, (v3_ordinal1(esk2_1(X1))|v4_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.42  cnf(c_0_85, negated_conjecture, (~v4_ordinal1(esk3_0)|~r2_hidden(k2_xboole_0(esk4_0,k1_tarski(esk4_0)),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_69])).
% 0.20/0.42  cnf(c_0_86, negated_conjecture, (v4_ordinal1(esk3_0)|esk3_0!=k2_xboole_0(X1,k1_tarski(X1))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_81, c_0_13])).
% 0.20/0.42  cnf(c_0_87, plain, (k2_xboole_0(esk2_1(X1),k1_tarski(esk2_1(X1)))=X1|v4_ordinal1(X1)|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])).
% 0.20/0.42  cnf(c_0_88, negated_conjecture, (~v4_ordinal1(esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_23]), c_0_40])]), c_0_53])).
% 0.20/0.42  cnf(c_0_89, negated_conjecture, (~v3_ordinal1(esk2_1(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])]), c_0_40])]), c_0_88])).
% 0.20/0.42  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_84]), c_0_40])]), c_0_88]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 91
% 0.20/0.42  # Proof object clause steps            : 70
% 0.20/0.42  # Proof object formula steps           : 21
% 0.20/0.42  # Proof object conjectures             : 26
% 0.20/0.42  # Proof object clause conjectures      : 23
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 21
% 0.20/0.42  # Proof object initial formulas used   : 10
% 0.20/0.42  # Proof object generating inferences   : 33
% 0.20/0.42  # Proof object simplifying inferences  : 58
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 10
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 25
% 0.20/0.42  # Removed in clause preprocessing      : 2
% 0.20/0.42  # Initial clauses in saturation        : 23
% 0.20/0.42  # Processed clauses                    : 526
% 0.20/0.42  # ...of these trivial                  : 1
% 0.20/0.42  # ...subsumed                          : 319
% 0.20/0.42  # ...remaining for further processing  : 206
% 0.20/0.42  # Other redundant clauses eliminated   : 4
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 34
% 0.20/0.42  # Backward-rewritten                   : 5
% 0.20/0.42  # Generated clauses                    : 1207
% 0.20/0.42  # ...of the previous two non-trivial   : 1061
% 0.20/0.42  # Contextual simplify-reflections      : 59
% 0.20/0.42  # Paramodulations                      : 1195
% 0.20/0.42  # Factorizations                       : 8
% 0.20/0.42  # Equation resolutions                 : 4
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 166
% 0.20/0.42  #    Positive orientable unit clauses  : 4
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 9
% 0.20/0.42  #    Non-unit-clauses                  : 153
% 0.20/0.42  # Current number of unprocessed clauses: 505
% 0.20/0.42  # ...number of literals in the above   : 2831
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 40
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 5713
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 1805
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 246
% 0.20/0.42  # Unit Clause-clause subsumption calls : 189
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 6
% 0.20/0.42  # BW rewrite match successes           : 2
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 33456
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.073 s
% 0.20/0.42  # System time              : 0.003 s
% 0.20/0.42  # Total time               : 0.076 s
% 0.20/0.42  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
