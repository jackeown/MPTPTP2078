%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:34 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 (13608 expanded)
%              Number of clauses        :   76 (6286 expanded)
%              Number of leaves         :   12 (3480 expanded)
%              Depth                    :   23
%              Number of atoms          :  325 (45803 expanded)
%              Number of equality atoms :   51 (9780 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(t14_ordinal1,axiom,(
    ! [X1] : X1 != k1_ordinal1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(t41_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v4_ordinal1(X1)
      <=> ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X2,X1)
             => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_ordinal1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(t33_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(c_0_12,plain,(
    ! [X17,X18] :
      ( ( ~ r2_hidden(X17,k1_ordinal1(X18))
        | r1_ordinal1(X17,X18)
        | ~ v3_ordinal1(X18)
        | ~ v3_ordinal1(X17) )
      & ( ~ r1_ordinal1(X17,X18)
        | r2_hidden(X17,k1_ordinal1(X18))
        | ~ v3_ordinal1(X18)
        | ~ v3_ordinal1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).

fof(c_0_13,plain,(
    ! [X5] : k1_ordinal1(X5) = k2_xboole_0(X5,k1_tarski(X5)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_14,plain,(
    ! [X9,X10] :
      ( ( ~ r2_hidden(X9,k1_ordinal1(X10))
        | r2_hidden(X9,X10)
        | X9 = X10 )
      & ( ~ r2_hidden(X9,X10)
        | r2_hidden(X9,k1_ordinal1(X10)) )
      & ( X9 != X10
        | r2_hidden(X9,k1_ordinal1(X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_15,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r2_hidden(X1,k1_ordinal1(X2))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X6,X7] :
      ( ( ~ r1_ordinal1(X6,X7)
        | r1_tarski(X6,X7)
        | ~ v3_ordinal1(X6)
        | ~ v3_ordinal1(X7) )
      & ( ~ r1_tarski(X6,X7)
        | r1_ordinal1(X6,X7)
        | ~ v3_ordinal1(X6)
        | ~ v3_ordinal1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_19,plain,
    ( r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_16])).

fof(c_0_21,plain,(
    ! [X3,X4] :
      ( ( r1_tarski(X3,X4)
        | X3 != X4 )
      & ( r1_tarski(X4,X3)
        | X3 != X4 )
      & ( ~ r1_tarski(X3,X4)
        | ~ r1_tarski(X4,X3)
        | X3 = X4 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_26,plain,(
    ! [X8] : r2_hidden(X8,k1_ordinal1(X8)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

fof(c_0_27,plain,(
    ! [X11] : X11 != k1_ordinal1(X11) ),
    inference(variable_rename,[status(thm)],[t14_ordinal1])).

fof(c_0_28,plain,(
    ! [X14] :
      ( ~ v3_ordinal1(X14)
      | v3_ordinal1(k1_ordinal1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( X1 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,plain,(
    ! [X19,X20] :
      ( ( ~ v4_ordinal1(X19)
        | ~ v3_ordinal1(X20)
        | ~ r2_hidden(X20,X19)
        | r2_hidden(k1_ordinal1(X20),X19)
        | ~ v3_ordinal1(X19) )
      & ( v3_ordinal1(esk1_1(X19))
        | v4_ordinal1(X19)
        | ~ v3_ordinal1(X19) )
      & ( r2_hidden(esk1_1(X19),X19)
        | v4_ordinal1(X19)
        | ~ v3_ordinal1(X19) )
      & ( ~ r2_hidden(k1_ordinal1(esk1_1(X19)),X19)
        | v4_ordinal1(X19)
        | ~ v3_ordinal1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_ordinal1])])])])])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_25])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_16])).

cnf(c_0_36,plain,
    ( X1 != k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_16])).

cnf(c_0_37,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_32,c_0_16])).

cnf(c_0_38,plain,
    ( r2_hidden(k1_ordinal1(X2),X1)
    | ~ v4_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_39,negated_conjecture,(
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

cnf(c_0_40,plain,
    ( ~ r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_41,plain,
    ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ v4_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_38,c_0_16])).

fof(c_0_42,negated_conjecture,(
    ! [X23] :
      ( v3_ordinal1(esk2_0)
      & ( v3_ordinal1(esk3_0)
        | ~ v4_ordinal1(esk2_0) )
      & ( esk2_0 = k1_ordinal1(esk3_0)
        | ~ v4_ordinal1(esk2_0) )
      & ( v4_ordinal1(esk2_0)
        | ~ v4_ordinal1(esk2_0) )
      & ( v3_ordinal1(esk3_0)
        | ~ v3_ordinal1(X23)
        | esk2_0 != k1_ordinal1(X23) )
      & ( esk2_0 = k1_ordinal1(esk3_0)
        | ~ v3_ordinal1(X23)
        | esk2_0 != k1_ordinal1(X23) )
      & ( v4_ordinal1(esk2_0)
        | ~ v3_ordinal1(X23)
        | esk2_0 != k1_ordinal1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_39])])])])])])).

cnf(c_0_43,plain,
    ( ~ v4_ordinal1(X1)
    | ~ r2_hidden(X1,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( esk2_0 = k1_ordinal1(esk3_0)
    | ~ v4_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_45,plain,
    ( v3_ordinal1(esk1_1(X1))
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,plain,
    ( ~ v4_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_41]),c_0_35])]),c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( esk2_0 = k2_xboole_0(esk3_0,k1_tarski(esk3_0))
    | ~ v4_ordinal1(esk2_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( v3_ordinal1(esk3_0)
    | ~ v4_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_50,plain,(
    ! [X12,X13] :
      ( ~ v3_ordinal1(X12)
      | ~ v3_ordinal1(X13)
      | r2_hidden(X12,X13)
      | X12 = X13
      | r2_hidden(X13,X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

cnf(c_0_51,negated_conjecture,
    ( v4_ordinal1(esk2_0)
    | v3_ordinal1(esk1_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( ~ v4_ordinal1(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( v3_ordinal1(esk1_1(esk2_0)) ),
    inference(sr,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( X1 = esk1_1(esk2_0)
    | r2_hidden(X1,esk1_1(esk2_0))
    | r2_hidden(esk1_1(esk2_0),X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_57,negated_conjecture,
    ( k2_xboole_0(X1,k1_tarski(X1)) = esk1_1(esk2_0)
    | r2_hidden(esk1_1(esk2_0),k2_xboole_0(X1,k1_tarski(X1)))
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk1_1(esk2_0))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_37])).

cnf(c_0_58,negated_conjecture,
    ( v4_ordinal1(esk2_0)
    | r2_hidden(esk1_1(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_46])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,k1_tarski(X1)) = X2
    | ~ r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_20])).

cnf(c_0_60,negated_conjecture,
    ( k2_xboole_0(esk2_0,k1_tarski(esk2_0)) = esk1_1(esk2_0)
    | r2_hidden(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk1_1(esk2_0))
    | r2_hidden(esk1_1(esk2_0),k2_xboole_0(esk2_0,k1_tarski(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_46])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_1(esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[c_0_58,c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( X1 = esk2_0
    | r2_hidden(X1,esk2_0)
    | r2_hidden(esk2_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_46])).

cnf(c_0_63,negated_conjecture,
    ( k2_xboole_0(esk2_0,k1_tarski(esk2_0)) = esk1_1(esk2_0)
    | r2_hidden(esk1_1(esk2_0),k2_xboole_0(esk2_0,k1_tarski(esk2_0)))
    | ~ v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_54])])).

cnf(c_0_64,plain,
    ( v4_ordinal1(X1)
    | ~ r2_hidden(k1_ordinal1(esk1_1(X1)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_65,negated_conjecture,
    ( k2_xboole_0(X1,k1_tarski(X1)) = esk2_0
    | r2_hidden(esk2_0,k2_xboole_0(X1,k1_tarski(X1)))
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk2_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_37])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_67,plain,(
    ! [X15,X16] :
      ( ( ~ r2_hidden(X15,X16)
        | r1_ordinal1(k1_ordinal1(X15),X16)
        | ~ v3_ordinal1(X16)
        | ~ v3_ordinal1(X15) )
      & ( ~ r1_ordinal1(k1_ordinal1(X15),X16)
        | r2_hidden(X15,X16)
        | ~ v3_ordinal1(X16)
        | ~ v3_ordinal1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).

cnf(c_0_68,negated_conjecture,
    ( k2_xboole_0(esk2_0,k1_tarski(esk2_0)) = esk1_1(esk2_0)
    | r2_hidden(esk1_1(esk2_0),k2_xboole_0(esk2_0,k1_tarski(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_37]),c_0_46])])).

cnf(c_0_69,plain,
    ( v4_ordinal1(X1)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(k2_xboole_0(esk1_1(X1),k1_tarski(esk1_1(X1))),X1) ),
    inference(rw,[status(thm)],[c_0_64,c_0_16])).

cnf(c_0_70,negated_conjecture,
    ( k2_xboole_0(esk1_1(esk2_0),k1_tarski(esk1_1(esk2_0))) = esk2_0
    | r2_hidden(k2_xboole_0(esk1_1(esk2_0),k1_tarski(esk1_1(esk2_0))),esk2_0)
    | r2_hidden(esk2_0,k2_xboole_0(esk1_1(esk2_0),k1_tarski(esk1_1(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_54])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r1_ordinal1(X1,X2) ),
    inference(rw,[status(thm)],[c_0_66,c_0_16])).

cnf(c_0_72,plain,
    ( r1_ordinal1(k1_ordinal1(X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_74,plain,
    ( v4_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | r2_hidden(esk1_1(k2_xboole_0(X1,k1_tarski(X1))),k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_37])).

cnf(c_0_75,negated_conjecture,
    ( k2_xboole_0(esk2_0,k1_tarski(esk2_0)) = esk1_1(esk2_0)
    | r1_ordinal1(esk1_1(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_68]),c_0_46]),c_0_54])])).

cnf(c_0_76,negated_conjecture,
    ( v4_ordinal1(esk2_0)
    | ~ v3_ordinal1(X1)
    | esk2_0 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_77,negated_conjecture,
    ( k2_xboole_0(esk1_1(esk2_0),k1_tarski(esk1_1(esk2_0))) = esk2_0
    | r2_hidden(esk2_0,k2_xboole_0(esk1_1(esk2_0),k1_tarski(esk1_1(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_46])]),c_0_52])).

cnf(c_0_78,plain,
    ( ~ r1_ordinal1(k2_xboole_0(esk1_1(k2_xboole_0(X1,k1_tarski(X1))),k1_tarski(esk1_1(k2_xboole_0(X1,k1_tarski(X1))))),X1)
    | ~ v3_ordinal1(k2_xboole_0(esk1_1(k2_xboole_0(X1,k1_tarski(X1))),k1_tarski(esk1_1(k2_xboole_0(X1,k1_tarski(X1))))))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_71]),c_0_37]),c_0_47])).

cnf(c_0_79,plain,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_16])).

cnf(c_0_80,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_73,c_0_16])).

cnf(c_0_81,negated_conjecture,
    ( v4_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))
    | r2_hidden(esk1_1(k2_xboole_0(esk2_0,k1_tarski(esk2_0))),k2_xboole_0(esk2_0,k1_tarski(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_46])).

cnf(c_0_82,plain,
    ( v4_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | v3_ordinal1(esk1_1(k2_xboole_0(X1,k1_tarski(X1))))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_37])).

cnf(c_0_83,negated_conjecture,
    ( r1_ordinal1(esk1_1(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_75]),c_0_61]),c_0_46])])).

cnf(c_0_84,negated_conjecture,
    ( v4_ordinal1(esk2_0)
    | esk2_0 != k2_xboole_0(X1,k1_tarski(X1))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_76,c_0_16])).

cnf(c_0_85,negated_conjecture,
    ( k2_xboole_0(esk1_1(esk2_0),k1_tarski(esk1_1(esk2_0))) = esk2_0
    | r1_ordinal1(esk2_0,esk1_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_77]),c_0_54]),c_0_46])])).

cnf(c_0_86,plain,
    ( ~ r2_hidden(esk1_1(k2_xboole_0(X1,k1_tarski(X1))),X1)
    | ~ v3_ordinal1(esk1_1(k2_xboole_0(X1,k1_tarski(X1))))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_37])).

cnf(c_0_87,negated_conjecture,
    ( esk1_1(k2_xboole_0(esk2_0,k1_tarski(esk2_0))) = esk2_0
    | v4_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))
    | r2_hidden(esk1_1(k2_xboole_0(esk2_0,k1_tarski(esk2_0))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( v4_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))
    | v3_ordinal1(esk1_1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_46])).

cnf(c_0_89,negated_conjecture,
    ( v4_ordinal1(esk1_1(esk2_0))
    | v4_ordinal1(esk2_0)
    | v3_ordinal1(esk1_1(esk1_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_51])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(esk1_1(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_83]),c_0_46]),c_0_54])])).

cnf(c_0_91,negated_conjecture,
    ( r1_ordinal1(esk2_0,esk1_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_54])]),c_0_52])).

cnf(c_0_92,negated_conjecture,
    ( esk1_1(k2_xboole_0(esk2_0,k1_tarski(esk2_0))) = esk2_0
    | v4_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_46])]),c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( v4_ordinal1(esk1_1(esk2_0))
    | v3_ordinal1(esk1_1(esk1_1(esk2_0))) ),
    inference(sr,[status(thm)],[c_0_89,c_0_52])).

cnf(c_0_94,negated_conjecture,
    ( esk1_1(esk2_0) = esk2_0
    | ~ r1_tarski(esk2_0,esk1_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_91]),c_0_54]),c_0_46])])).

cnf(c_0_96,negated_conjecture,
    ( v4_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))
    | ~ r2_hidden(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_92]),c_0_46])])).

cnf(c_0_97,negated_conjecture,
    ( v4_ordinal1(esk1_1(esk1_1(esk2_0)))
    | v4_ordinal1(esk1_1(esk2_0))
    | r2_hidden(esk1_1(esk1_1(esk1_1(esk2_0))),esk1_1(esk1_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( esk1_1(esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95])])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_96]),c_0_46])])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98])]),c_0_52]),c_0_99]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:35:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.41  #
% 0.21/0.41  # Preprocessing time       : 0.028 s
% 0.21/0.41  # Presaturation interreduction done
% 0.21/0.41  
% 0.21/0.41  # Proof found!
% 0.21/0.41  # SZS status Theorem
% 0.21/0.41  # SZS output start CNFRefutation
% 0.21/0.41  fof(t34_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 0.21/0.41  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.21/0.41  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.21/0.41  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.21/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.41  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.21/0.41  fof(t14_ordinal1, axiom, ![X1]:X1!=k1_ordinal1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_ordinal1)).
% 0.21/0.41  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.21/0.41  fof(t41_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_ordinal1)).
% 0.21/0.41  fof(t42_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(~((~(v4_ordinal1(X1))&![X2]:(v3_ordinal1(X2)=>X1!=k1_ordinal1(X2))))&~((?[X2]:(v3_ordinal1(X2)&X1=k1_ordinal1(X2))&v4_ordinal1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_ordinal1)).
% 0.21/0.41  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.21/0.41  fof(t33_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 0.21/0.41  fof(c_0_12, plain, ![X17, X18]:((~r2_hidden(X17,k1_ordinal1(X18))|r1_ordinal1(X17,X18)|~v3_ordinal1(X18)|~v3_ordinal1(X17))&(~r1_ordinal1(X17,X18)|r2_hidden(X17,k1_ordinal1(X18))|~v3_ordinal1(X18)|~v3_ordinal1(X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).
% 0.21/0.41  fof(c_0_13, plain, ![X5]:k1_ordinal1(X5)=k2_xboole_0(X5,k1_tarski(X5)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.21/0.41  fof(c_0_14, plain, ![X9, X10]:((~r2_hidden(X9,k1_ordinal1(X10))|(r2_hidden(X9,X10)|X9=X10))&((~r2_hidden(X9,X10)|r2_hidden(X9,k1_ordinal1(X10)))&(X9!=X10|r2_hidden(X9,k1_ordinal1(X10))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.21/0.41  cnf(c_0_15, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,k1_ordinal1(X2))|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.41  cnf(c_0_16, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.41  cnf(c_0_17, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.41  fof(c_0_18, plain, ![X6, X7]:((~r1_ordinal1(X6,X7)|r1_tarski(X6,X7)|(~v3_ordinal1(X6)|~v3_ordinal1(X7)))&(~r1_tarski(X6,X7)|r1_ordinal1(X6,X7)|(~v3_ordinal1(X6)|~v3_ordinal1(X7)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.21/0.41  cnf(c_0_19, plain, (r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.41  cnf(c_0_20, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_16])).
% 0.21/0.41  fof(c_0_21, plain, ![X3, X4]:(((r1_tarski(X3,X4)|X3!=X4)&(r1_tarski(X4,X3)|X3!=X4))&(~r1_tarski(X3,X4)|~r1_tarski(X4,X3)|X3=X4)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.41  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.41  cnf(c_0_23, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.41  cnf(c_0_24, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.41  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.21/0.41  fof(c_0_26, plain, ![X8]:r2_hidden(X8,k1_ordinal1(X8)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 0.21/0.41  fof(c_0_27, plain, ![X11]:X11!=k1_ordinal1(X11), inference(variable_rename,[status(thm)],[t14_ordinal1])).
% 0.21/0.41  fof(c_0_28, plain, ![X14]:(~v3_ordinal1(X14)|v3_ordinal1(k1_ordinal1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.21/0.41  cnf(c_0_29, plain, (X1=X2|~r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.41  cnf(c_0_30, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.41  cnf(c_0_31, plain, (X1!=k1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.41  cnf(c_0_32, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.41  fof(c_0_33, plain, ![X19, X20]:((~v4_ordinal1(X19)|(~v3_ordinal1(X20)|(~r2_hidden(X20,X19)|r2_hidden(k1_ordinal1(X20),X19)))|~v3_ordinal1(X19))&((v3_ordinal1(esk1_1(X19))|v4_ordinal1(X19)|~v3_ordinal1(X19))&((r2_hidden(esk1_1(X19),X19)|v4_ordinal1(X19)|~v3_ordinal1(X19))&(~r2_hidden(k1_ordinal1(esk1_1(X19)),X19)|v4_ordinal1(X19)|~v3_ordinal1(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_ordinal1])])])])])).
% 0.21/0.41  cnf(c_0_34, plain, (X1=X2|~r2_hidden(X2,X1)|~r2_hidden(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(spm,[status(thm)],[c_0_29, c_0_25])).
% 0.21/0.41  cnf(c_0_35, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_30, c_0_16])).
% 0.21/0.41  cnf(c_0_36, plain, (X1!=k2_xboole_0(X1,k1_tarski(X1))), inference(rw,[status(thm)],[c_0_31, c_0_16])).
% 0.21/0.41  cnf(c_0_37, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_32, c_0_16])).
% 0.21/0.41  cnf(c_0_38, plain, (r2_hidden(k1_ordinal1(X2),X1)|~v4_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X2,X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.41  fof(c_0_39, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(~((~(v4_ordinal1(X1))&![X2]:(v3_ordinal1(X2)=>X1!=k1_ordinal1(X2))))&~((?[X2]:(v3_ordinal1(X2)&X1=k1_ordinal1(X2))&v4_ordinal1(X1)))))), inference(assume_negation,[status(cth)],[t42_ordinal1])).
% 0.21/0.41  cnf(c_0_40, plain, (~r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X1)|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37])).
% 0.21/0.41  cnf(c_0_41, plain, (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X1)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~v4_ordinal1(X1)|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_38, c_0_16])).
% 0.21/0.41  fof(c_0_42, negated_conjecture, ![X23]:(v3_ordinal1(esk2_0)&((((v3_ordinal1(esk3_0)|~v4_ordinal1(esk2_0))&(esk2_0=k1_ordinal1(esk3_0)|~v4_ordinal1(esk2_0)))&(v4_ordinal1(esk2_0)|~v4_ordinal1(esk2_0)))&(((v3_ordinal1(esk3_0)|(~v3_ordinal1(X23)|esk2_0!=k1_ordinal1(X23)))&(esk2_0=k1_ordinal1(esk3_0)|(~v3_ordinal1(X23)|esk2_0!=k1_ordinal1(X23))))&(v4_ordinal1(esk2_0)|(~v3_ordinal1(X23)|esk2_0!=k1_ordinal1(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_39])])])])])])).
% 0.21/0.41  cnf(c_0_43, plain, (~v4_ordinal1(X1)|~r2_hidden(X1,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.21/0.41  cnf(c_0_44, negated_conjecture, (esk2_0=k1_ordinal1(esk3_0)|~v4_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.41  cnf(c_0_45, plain, (v3_ordinal1(esk1_1(X1))|v4_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.41  cnf(c_0_46, negated_conjecture, (v3_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.41  cnf(c_0_47, plain, (~v4_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_41]), c_0_35])]), c_0_37])).
% 0.21/0.41  cnf(c_0_48, negated_conjecture, (esk2_0=k2_xboole_0(esk3_0,k1_tarski(esk3_0))|~v4_ordinal1(esk2_0)), inference(rw,[status(thm)],[c_0_44, c_0_16])).
% 0.21/0.41  cnf(c_0_49, negated_conjecture, (v3_ordinal1(esk3_0)|~v4_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.41  fof(c_0_50, plain, ![X12, X13]:(~v3_ordinal1(X12)|(~v3_ordinal1(X13)|(r2_hidden(X12,X13)|X12=X13|r2_hidden(X13,X12)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.21/0.41  cnf(c_0_51, negated_conjecture, (v4_ordinal1(esk2_0)|v3_ordinal1(esk1_1(esk2_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.21/0.41  cnf(c_0_52, negated_conjecture, (~v4_ordinal1(esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.21/0.41  cnf(c_0_53, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.41  cnf(c_0_54, negated_conjecture, (v3_ordinal1(esk1_1(esk2_0))), inference(sr,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.41  cnf(c_0_55, negated_conjecture, (X1=esk1_1(esk2_0)|r2_hidden(X1,esk1_1(esk2_0))|r2_hidden(esk1_1(esk2_0),X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.41  cnf(c_0_56, plain, (r2_hidden(esk1_1(X1),X1)|v4_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.41  cnf(c_0_57, negated_conjecture, (k2_xboole_0(X1,k1_tarski(X1))=esk1_1(esk2_0)|r2_hidden(esk1_1(esk2_0),k2_xboole_0(X1,k1_tarski(X1)))|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk1_1(esk2_0))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_37])).
% 0.21/0.41  cnf(c_0_58, negated_conjecture, (v4_ordinal1(esk2_0)|r2_hidden(esk1_1(esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_56, c_0_46])).
% 0.21/0.41  cnf(c_0_59, plain, (k2_xboole_0(X1,k1_tarski(X1))=X2|~r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X2)|~r2_hidden(X2,X1)|~v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X2)), inference(spm,[status(thm)],[c_0_34, c_0_20])).
% 0.21/0.41  cnf(c_0_60, negated_conjecture, (k2_xboole_0(esk2_0,k1_tarski(esk2_0))=esk1_1(esk2_0)|r2_hidden(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk1_1(esk2_0))|r2_hidden(esk1_1(esk2_0),k2_xboole_0(esk2_0,k1_tarski(esk2_0)))), inference(spm,[status(thm)],[c_0_57, c_0_46])).
% 0.21/0.41  cnf(c_0_61, negated_conjecture, (r2_hidden(esk1_1(esk2_0),esk2_0)), inference(sr,[status(thm)],[c_0_58, c_0_52])).
% 0.21/0.41  cnf(c_0_62, negated_conjecture, (X1=esk2_0|r2_hidden(X1,esk2_0)|r2_hidden(esk2_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_46])).
% 0.21/0.41  cnf(c_0_63, negated_conjecture, (k2_xboole_0(esk2_0,k1_tarski(esk2_0))=esk1_1(esk2_0)|r2_hidden(esk1_1(esk2_0),k2_xboole_0(esk2_0,k1_tarski(esk2_0)))|~v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_54])])).
% 0.21/0.41  cnf(c_0_64, plain, (v4_ordinal1(X1)|~r2_hidden(k1_ordinal1(esk1_1(X1)),X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.41  cnf(c_0_65, negated_conjecture, (k2_xboole_0(X1,k1_tarski(X1))=esk2_0|r2_hidden(esk2_0,k2_xboole_0(X1,k1_tarski(X1)))|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk2_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_62, c_0_37])).
% 0.21/0.41  cnf(c_0_66, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.41  fof(c_0_67, plain, ![X15, X16]:((~r2_hidden(X15,X16)|r1_ordinal1(k1_ordinal1(X15),X16)|~v3_ordinal1(X16)|~v3_ordinal1(X15))&(~r1_ordinal1(k1_ordinal1(X15),X16)|r2_hidden(X15,X16)|~v3_ordinal1(X16)|~v3_ordinal1(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).
% 0.21/0.41  cnf(c_0_68, negated_conjecture, (k2_xboole_0(esk2_0,k1_tarski(esk2_0))=esk1_1(esk2_0)|r2_hidden(esk1_1(esk2_0),k2_xboole_0(esk2_0,k1_tarski(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_37]), c_0_46])])).
% 0.21/0.41  cnf(c_0_69, plain, (v4_ordinal1(X1)|~v3_ordinal1(X1)|~r2_hidden(k2_xboole_0(esk1_1(X1),k1_tarski(esk1_1(X1))),X1)), inference(rw,[status(thm)],[c_0_64, c_0_16])).
% 0.21/0.41  cnf(c_0_70, negated_conjecture, (k2_xboole_0(esk1_1(esk2_0),k1_tarski(esk1_1(esk2_0)))=esk2_0|r2_hidden(k2_xboole_0(esk1_1(esk2_0),k1_tarski(esk1_1(esk2_0))),esk2_0)|r2_hidden(esk2_0,k2_xboole_0(esk1_1(esk2_0),k1_tarski(esk1_1(esk2_0))))), inference(spm,[status(thm)],[c_0_65, c_0_54])).
% 0.21/0.41  cnf(c_0_71, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r1_ordinal1(X1,X2)), inference(rw,[status(thm)],[c_0_66, c_0_16])).
% 0.21/0.41  cnf(c_0_72, plain, (r1_ordinal1(k1_ordinal1(X1),X2)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.21/0.41  cnf(c_0_73, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.41  cnf(c_0_74, plain, (v4_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|r2_hidden(esk1_1(k2_xboole_0(X1,k1_tarski(X1))),k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_56, c_0_37])).
% 0.21/0.41  cnf(c_0_75, negated_conjecture, (k2_xboole_0(esk2_0,k1_tarski(esk2_0))=esk1_1(esk2_0)|r1_ordinal1(esk1_1(esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_68]), c_0_46]), c_0_54])])).
% 0.21/0.41  cnf(c_0_76, negated_conjecture, (v4_ordinal1(esk2_0)|~v3_ordinal1(X1)|esk2_0!=k1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.41  cnf(c_0_77, negated_conjecture, (k2_xboole_0(esk1_1(esk2_0),k1_tarski(esk1_1(esk2_0)))=esk2_0|r2_hidden(esk2_0,k2_xboole_0(esk1_1(esk2_0),k1_tarski(esk1_1(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_46])]), c_0_52])).
% 0.21/0.41  cnf(c_0_78, plain, (~r1_ordinal1(k2_xboole_0(esk1_1(k2_xboole_0(X1,k1_tarski(X1))),k1_tarski(esk1_1(k2_xboole_0(X1,k1_tarski(X1))))),X1)|~v3_ordinal1(k2_xboole_0(esk1_1(k2_xboole_0(X1,k1_tarski(X1))),k1_tarski(esk1_1(k2_xboole_0(X1,k1_tarski(X1))))))|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_71]), c_0_37]), c_0_47])).
% 0.21/0.41  cnf(c_0_79, plain, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_72, c_0_16])).
% 0.21/0.41  cnf(c_0_80, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_73, c_0_16])).
% 0.21/0.41  cnf(c_0_81, negated_conjecture, (v4_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))|r2_hidden(esk1_1(k2_xboole_0(esk2_0,k1_tarski(esk2_0))),k2_xboole_0(esk2_0,k1_tarski(esk2_0)))), inference(spm,[status(thm)],[c_0_74, c_0_46])).
% 0.21/0.41  cnf(c_0_82, plain, (v4_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|v3_ordinal1(esk1_1(k2_xboole_0(X1,k1_tarski(X1))))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_37])).
% 0.21/0.41  cnf(c_0_83, negated_conjecture, (r1_ordinal1(esk1_1(esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_75]), c_0_61]), c_0_46])])).
% 0.21/0.41  cnf(c_0_84, negated_conjecture, (v4_ordinal1(esk2_0)|esk2_0!=k2_xboole_0(X1,k1_tarski(X1))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_76, c_0_16])).
% 0.21/0.41  cnf(c_0_85, negated_conjecture, (k2_xboole_0(esk1_1(esk2_0),k1_tarski(esk1_1(esk2_0)))=esk2_0|r1_ordinal1(esk2_0,esk1_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_77]), c_0_54]), c_0_46])])).
% 0.21/0.41  cnf(c_0_86, plain, (~r2_hidden(esk1_1(k2_xboole_0(X1,k1_tarski(X1))),X1)|~v3_ordinal1(esk1_1(k2_xboole_0(X1,k1_tarski(X1))))|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_37])).
% 0.21/0.41  cnf(c_0_87, negated_conjecture, (esk1_1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))=esk2_0|v4_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))|r2_hidden(esk1_1(k2_xboole_0(esk2_0,k1_tarski(esk2_0))),esk2_0)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.21/0.41  cnf(c_0_88, negated_conjecture, (v4_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))|v3_ordinal1(esk1_1(k2_xboole_0(esk2_0,k1_tarski(esk2_0))))), inference(spm,[status(thm)],[c_0_82, c_0_46])).
% 0.21/0.41  cnf(c_0_89, negated_conjecture, (v4_ordinal1(esk1_1(esk2_0))|v4_ordinal1(esk2_0)|v3_ordinal1(esk1_1(esk1_1(esk2_0)))), inference(spm,[status(thm)],[c_0_45, c_0_51])).
% 0.21/0.41  cnf(c_0_90, negated_conjecture, (r1_tarski(esk1_1(esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_83]), c_0_46]), c_0_54])])).
% 0.21/0.41  cnf(c_0_91, negated_conjecture, (r1_ordinal1(esk2_0,esk1_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_54])]), c_0_52])).
% 0.21/0.41  cnf(c_0_92, negated_conjecture, (esk1_1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))=esk2_0|v4_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_46])]), c_0_88])).
% 0.21/0.41  cnf(c_0_93, negated_conjecture, (v4_ordinal1(esk1_1(esk2_0))|v3_ordinal1(esk1_1(esk1_1(esk2_0)))), inference(sr,[status(thm)],[c_0_89, c_0_52])).
% 0.21/0.41  cnf(c_0_94, negated_conjecture, (esk1_1(esk2_0)=esk2_0|~r1_tarski(esk2_0,esk1_1(esk2_0))), inference(spm,[status(thm)],[c_0_24, c_0_90])).
% 0.21/0.41  cnf(c_0_95, negated_conjecture, (r1_tarski(esk2_0,esk1_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_91]), c_0_54]), c_0_46])])).
% 0.21/0.41  cnf(c_0_96, negated_conjecture, (v4_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))|~r2_hidden(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_92]), c_0_46])])).
% 0.21/0.41  cnf(c_0_97, negated_conjecture, (v4_ordinal1(esk1_1(esk1_1(esk2_0)))|v4_ordinal1(esk1_1(esk2_0))|r2_hidden(esk1_1(esk1_1(esk1_1(esk2_0))),esk1_1(esk1_1(esk2_0)))), inference(spm,[status(thm)],[c_0_56, c_0_93])).
% 0.21/0.41  cnf(c_0_98, negated_conjecture, (esk1_1(esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95])])).
% 0.21/0.41  cnf(c_0_99, negated_conjecture, (~r2_hidden(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_96]), c_0_46])])).
% 0.21/0.41  cnf(c_0_100, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_98]), c_0_98]), c_0_98]), c_0_98]), c_0_98]), c_0_98]), c_0_98]), c_0_98])]), c_0_52]), c_0_99]), ['proof']).
% 0.21/0.41  # SZS output end CNFRefutation
% 0.21/0.41  # Proof object total steps             : 101
% 0.21/0.41  # Proof object clause steps            : 76
% 0.21/0.41  # Proof object formula steps           : 25
% 0.21/0.41  # Proof object conjectures             : 41
% 0.21/0.41  # Proof object clause conjectures      : 38
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 20
% 0.21/0.41  # Proof object initial formulas used   : 12
% 0.21/0.41  # Proof object generating inferences   : 39
% 0.21/0.41  # Proof object simplifying inferences  : 70
% 0.21/0.41  # Training examples: 0 positive, 0 negative
% 0.21/0.41  # Parsed axioms                        : 12
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 28
% 0.21/0.41  # Removed in clause preprocessing      : 2
% 0.21/0.41  # Initial clauses in saturation        : 26
% 0.21/0.41  # Processed clauses                    : 329
% 0.21/0.41  # ...of these trivial                  : 1
% 0.21/0.41  # ...subsumed                          : 139
% 0.21/0.41  # ...remaining for further processing  : 189
% 0.21/0.41  # Other redundant clauses eliminated   : 3
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 17
% 0.21/0.41  # Backward-rewritten                   : 32
% 0.21/0.41  # Generated clauses                    : 769
% 0.21/0.41  # ...of the previous two non-trivial   : 686
% 0.21/0.41  # Contextual simplify-reflections      : 33
% 0.21/0.41  # Paramodulations                      : 763
% 0.21/0.41  # Factorizations                       : 0
% 0.21/0.41  # Equation resolutions                 : 3
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 110
% 0.21/0.41  #    Positive orientable unit clauses  : 5
% 0.21/0.41  #    Positive unorientable unit clauses: 0
% 0.21/0.41  #    Negative unit clauses             : 4
% 0.21/0.41  #    Non-unit-clauses                  : 101
% 0.21/0.41  # Current number of unprocessed clauses: 293
% 0.21/0.41  # ...number of literals in the above   : 1346
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 77
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 2861
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 1150
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 120
% 0.21/0.41  # Unit Clause-clause subsumption calls : 500
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 5
% 0.21/0.41  # BW rewrite match successes           : 5
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 24686
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.057 s
% 0.21/0.41  # System time              : 0.003 s
% 0.21/0.41  # Total time               : 0.060 s
% 0.21/0.41  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
