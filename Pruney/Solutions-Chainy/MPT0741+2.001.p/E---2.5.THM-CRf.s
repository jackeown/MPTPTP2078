%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:13 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 651 expanded)
%              Number of clauses        :   55 ( 290 expanded)
%              Number of leaves         :   12 ( 155 expanded)
%              Depth                    :   19
%              Number of atoms          :  233 (2502 expanded)
%              Number of equality atoms :   15 ( 132 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc2_ordinal1,axiom,(
    ! [X1] :
      ( ( v1_ordinal1(X1)
        & v2_ordinal1(X1) )
     => v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_ordinal1)).

fof(d3_ordinal1,axiom,(
    ! [X1] :
      ( v2_ordinal1(X1)
    <=> ! [X2,X3] :
          ~ ( r2_hidden(X2,X1)
            & r2_hidden(X3,X1)
            & ~ r2_hidden(X2,X3)
            & X2 != X3
            & ~ r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_ordinal1)).

fof(t31_ordinal1,conjecture,(
    ! [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
         => ( v3_ordinal1(X2)
            & r1_tarski(X2,X1) ) )
     => v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_ordinal1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(t22_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ! [X3] :
              ( v3_ordinal1(X3)
             => ( ( r1_tarski(X1,X2)
                  & r2_hidden(X2,X3) )
               => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(c_0_12,plain,(
    ! [X5] :
      ( ~ v1_ordinal1(X5)
      | ~ v2_ordinal1(X5)
      | v3_ordinal1(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_ordinal1])])).

fof(c_0_13,plain,(
    ! [X11,X12,X13,X14] :
      ( ( ~ v2_ordinal1(X11)
        | ~ r2_hidden(X12,X11)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X12,X13)
        | X12 = X13
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_1(X14),X14)
        | v2_ordinal1(X14) )
      & ( r2_hidden(esk3_1(X14),X14)
        | v2_ordinal1(X14) )
      & ( ~ r2_hidden(esk2_1(X14),esk3_1(X14))
        | v2_ordinal1(X14) )
      & ( esk2_1(X14) != esk3_1(X14)
        | v2_ordinal1(X14) )
      & ( ~ r2_hidden(esk3_1(X14),esk2_1(X14))
        | v2_ordinal1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_ordinal1])])])])])])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X1)
           => ( v3_ordinal1(X2)
              & r1_tarski(X2,X1) ) )
       => v3_ordinal1(X1) ) ),
    inference(assume_negation,[status(cth)],[t31_ordinal1])).

cnf(c_0_15,plain,
    ( v3_ordinal1(X1)
    | ~ v1_ordinal1(X1)
    | ~ v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_ordinal1(X7)
        | ~ r2_hidden(X8,X7)
        | r1_tarski(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_ordinal1(X9) )
      & ( ~ r1_tarski(esk1_1(X9),X9)
        | v1_ordinal1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

cnf(c_0_18,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,(
    ! [X30] :
      ( ( v3_ordinal1(X30)
        | ~ r2_hidden(X30,esk4_0) )
      & ( r1_tarski(X30,esk4_0)
        | ~ r2_hidden(X30,esk4_0) )
      & ~ v3_ordinal1(esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v3_ordinal1(X1)
    | ~ v1_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | v3_ordinal1(X1)
    | ~ v1_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( ~ v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | r2_hidden(esk3_1(X1),X1)
    | v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | r2_hidden(esk2_1(X1),X1)
    | v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk3_1(esk4_0),esk4_0)
    | r2_hidden(esk1_1(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),esk4_0)
    | r2_hidden(esk1_1(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_25])).

cnf(c_0_29,plain,
    ( v1_ordinal1(X1)
    | ~ r1_tarski(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk1_1(esk4_0),esk4_0)
    | r2_hidden(esk3_1(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk1_1(esk4_0),esk4_0)
    | r2_hidden(esk2_1(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk3_1(esk4_0),esk4_0)
    | v1_ordinal1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),esk4_0)
    | v1_ordinal1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_31])).

fof(c_0_34,plain,(
    ! [X21,X22,X23] :
      ( ~ v1_ordinal1(X21)
      | ~ v3_ordinal1(X22)
      | ~ v3_ordinal1(X23)
      | ~ r1_tarski(X21,X22)
      | ~ r2_hidden(X22,X23)
      | r2_hidden(X21,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_ordinal1])])])).

fof(c_0_35,plain,(
    ! [X24,X25] :
      ( ~ v3_ordinal1(X25)
      | ~ r2_hidden(X24,X25)
      | v3_ordinal1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

fof(c_0_36,plain,(
    ! [X4] :
      ( ( v1_ordinal1(X4)
        | ~ v3_ordinal1(X4) )
      & ( v2_ordinal1(X4)
        | ~ v3_ordinal1(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

cnf(c_0_37,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk3_1(esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_32]),c_0_23])).

fof(c_0_39,plain,(
    ! [X28] :
      ( ~ v3_ordinal1(X28)
      | v3_ordinal1(k1_ordinal1(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

fof(c_0_40,plain,(
    ! [X6] : k1_ordinal1(X6) = k2_xboole_0(X6,k1_tarski(X6)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_41,plain,(
    ! [X17,X18] :
      ( ( ~ r1_ordinal1(X17,X18)
        | r1_tarski(X17,X18)
        | ~ v3_ordinal1(X17)
        | ~ v3_ordinal1(X18) )
      & ( ~ r1_tarski(X17,X18)
        | r1_ordinal1(X17,X18)
        | ~ v3_ordinal1(X17)
        | ~ v3_ordinal1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_33]),c_0_23])).

fof(c_0_43,plain,(
    ! [X26,X27] :
      ( ~ v3_ordinal1(X26)
      | ~ v3_ordinal1(X27)
      | r1_ordinal1(X26,X27)
      | r2_hidden(X27,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( v3_ordinal1(esk3_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_48,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( v3_ordinal1(esk2_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_42])).

cnf(c_0_52,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_53,plain,(
    ! [X19,X20] :
      ( ( ~ r2_hidden(X19,k1_ordinal1(X20))
        | r2_hidden(X19,X20)
        | X19 = X20 )
      & ( ~ r2_hidden(X19,X20)
        | r2_hidden(X19,k1_ordinal1(X20)) )
      & ( X19 != X20
        | r2_hidden(X19,k1_ordinal1(X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(csr,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( v1_ordinal1(esk3_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(X1,esk2_1(esk4_0))
    | ~ r1_ordinal1(X1,esk2_1(esk4_0))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( r1_ordinal1(X1,esk2_1(esk4_0))
    | r2_hidden(esk2_1(esk4_0),X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_51])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk3_1(esk4_0),X1)
    | ~ r1_tarski(esk3_1(esk4_0),X2)
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk2_1(esk4_0),k1_tarski(esk2_1(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk3_1(esk4_0),esk2_1(esk4_0))
    | ~ r1_ordinal1(esk3_1(esk4_0),esk2_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_47])).

cnf(c_0_63,negated_conjecture,
    ( r1_ordinal1(esk3_1(esk4_0),esk2_1(esk4_0))
    | r2_hidden(esk2_1(esk4_0),esk3_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_47])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | X1 != X2 ),
    inference(rw,[status(thm)],[c_0_59,c_0_49])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk3_1(esk4_0),k2_xboole_0(esk2_1(esk4_0),k1_tarski(esk2_1(esk4_0))))
    | ~ r1_tarski(esk3_1(esk4_0),X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk2_1(esk4_0),k1_tarski(esk2_1(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk3_1(esk4_0),esk2_1(esk4_0))
    | r2_hidden(esk2_1(esk4_0),esk3_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_69,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_65,c_0_49])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk3_1(esk4_0),k2_xboole_0(esk2_1(esk4_0),k1_tarski(esk2_1(esk4_0))))
    | r2_hidden(esk2_1(esk4_0),esk3_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])])).

cnf(c_0_71,plain,
    ( v2_ordinal1(X1)
    | esk2_1(X1) != esk3_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_72,negated_conjecture,
    ( esk3_1(esk4_0) = esk2_1(esk4_0)
    | r2_hidden(esk2_1(esk4_0),esk3_1(esk4_0))
    | r2_hidden(esk3_1(esk4_0),esk2_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_73,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk3_1(X1),esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_74,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk2_1(X1),esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_75,negated_conjecture,
    ( v2_ordinal1(esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_74])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_ordinal1(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_75]),c_0_23])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk1_1(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_21])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk1_1(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_77])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_78]),c_0_76]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:00:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.20/0.38  # and selection function SelectSmallestOrientable.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(cc2_ordinal1, axiom, ![X1]:((v1_ordinal1(X1)&v2_ordinal1(X1))=>v3_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_ordinal1)).
% 0.20/0.38  fof(d3_ordinal1, axiom, ![X1]:(v2_ordinal1(X1)<=>![X2, X3]:~(((((r2_hidden(X2,X1)&r2_hidden(X3,X1))&~(r2_hidden(X2,X3)))&X2!=X3)&~(r2_hidden(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_ordinal1)).
% 0.20/0.38  fof(t31_ordinal1, conjecture, ![X1]:(![X2]:(r2_hidden(X2,X1)=>(v3_ordinal1(X2)&r1_tarski(X2,X1)))=>v3_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_ordinal1)).
% 0.20/0.38  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.20/0.38  fof(t22_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>![X3]:(v3_ordinal1(X3)=>((r1_tarski(X1,X2)&r2_hidden(X2,X3))=>r2_hidden(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_ordinal1)).
% 0.20/0.38  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.20/0.38  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.20/0.38  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.20/0.38  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.20/0.38  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.20/0.38  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.20/0.38  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.20/0.38  fof(c_0_12, plain, ![X5]:(~v1_ordinal1(X5)|~v2_ordinal1(X5)|v3_ordinal1(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_ordinal1])])).
% 0.20/0.38  fof(c_0_13, plain, ![X11, X12, X13, X14]:((~v2_ordinal1(X11)|(~r2_hidden(X12,X11)|~r2_hidden(X13,X11)|r2_hidden(X12,X13)|X12=X13|r2_hidden(X13,X12)))&(((((r2_hidden(esk2_1(X14),X14)|v2_ordinal1(X14))&(r2_hidden(esk3_1(X14),X14)|v2_ordinal1(X14)))&(~r2_hidden(esk2_1(X14),esk3_1(X14))|v2_ordinal1(X14)))&(esk2_1(X14)!=esk3_1(X14)|v2_ordinal1(X14)))&(~r2_hidden(esk3_1(X14),esk2_1(X14))|v2_ordinal1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_ordinal1])])])])])])])).
% 0.20/0.38  fof(c_0_14, negated_conjecture, ~(![X1]:(![X2]:(r2_hidden(X2,X1)=>(v3_ordinal1(X2)&r1_tarski(X2,X1)))=>v3_ordinal1(X1))), inference(assume_negation,[status(cth)],[t31_ordinal1])).
% 0.20/0.38  cnf(c_0_15, plain, (v3_ordinal1(X1)|~v1_ordinal1(X1)|~v2_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_16, plain, (r2_hidden(esk3_1(X1),X1)|v2_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_17, plain, ![X7, X8, X9]:((~v1_ordinal1(X7)|(~r2_hidden(X8,X7)|r1_tarski(X8,X7)))&((r2_hidden(esk1_1(X9),X9)|v1_ordinal1(X9))&(~r1_tarski(esk1_1(X9),X9)|v1_ordinal1(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.20/0.38  cnf(c_0_18, plain, (r2_hidden(esk2_1(X1),X1)|v2_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_19, negated_conjecture, ![X30]:(((v3_ordinal1(X30)|~r2_hidden(X30,esk4_0))&(r1_tarski(X30,esk4_0)|~r2_hidden(X30,esk4_0)))&~v3_ordinal1(esk4_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])])).
% 0.20/0.38  cnf(c_0_20, plain, (r2_hidden(esk3_1(X1),X1)|v3_ordinal1(X1)|~v1_ordinal1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.38  cnf(c_0_21, plain, (r2_hidden(esk1_1(X1),X1)|v1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_22, plain, (r2_hidden(esk2_1(X1),X1)|v3_ordinal1(X1)|~v1_ordinal1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_18])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (~v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_24, plain, (r2_hidden(esk1_1(X1),X1)|r2_hidden(esk3_1(X1),X1)|v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.38  cnf(c_0_25, plain, (r2_hidden(esk1_1(X1),X1)|r2_hidden(esk2_1(X1),X1)|v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (r1_tarski(X1,esk4_0)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(esk3_1(esk4_0),esk4_0)|r2_hidden(esk1_1(esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk2_1(esk4_0),esk4_0)|r2_hidden(esk1_1(esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_25])).
% 0.20/0.38  cnf(c_0_29, plain, (v1_ordinal1(X1)|~r1_tarski(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (r1_tarski(esk1_1(esk4_0),esk4_0)|r2_hidden(esk3_1(esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (r1_tarski(esk1_1(esk4_0),esk4_0)|r2_hidden(esk2_1(esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_28])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(esk3_1(esk4_0),esk4_0)|v1_ordinal1(esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (r2_hidden(esk2_1(esk4_0),esk4_0)|v1_ordinal1(esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_31])).
% 0.20/0.38  fof(c_0_34, plain, ![X21, X22, X23]:(~v1_ordinal1(X21)|(~v3_ordinal1(X22)|(~v3_ordinal1(X23)|(~r1_tarski(X21,X22)|~r2_hidden(X22,X23)|r2_hidden(X21,X23))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_ordinal1])])])).
% 0.20/0.38  fof(c_0_35, plain, ![X24, X25]:(~v3_ordinal1(X25)|(~r2_hidden(X24,X25)|v3_ordinal1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.20/0.38  fof(c_0_36, plain, ![X4]:((v1_ordinal1(X4)|~v3_ordinal1(X4))&(v2_ordinal1(X4)|~v3_ordinal1(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk3_1(esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_32]), c_0_23])).
% 0.20/0.38  fof(c_0_39, plain, ![X28]:(~v3_ordinal1(X28)|v3_ordinal1(k1_ordinal1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.20/0.38  fof(c_0_40, plain, ![X6]:k1_ordinal1(X6)=k2_xboole_0(X6,k1_tarski(X6)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.20/0.38  fof(c_0_41, plain, ![X17, X18]:((~r1_ordinal1(X17,X18)|r1_tarski(X17,X18)|(~v3_ordinal1(X17)|~v3_ordinal1(X18)))&(~r1_tarski(X17,X18)|r1_ordinal1(X17,X18)|(~v3_ordinal1(X17)|~v3_ordinal1(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (r2_hidden(esk2_1(esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_33]), c_0_23])).
% 0.20/0.38  fof(c_0_43, plain, ![X26, X27]:(~v3_ordinal1(X26)|(~v3_ordinal1(X27)|(r1_ordinal1(X26,X27)|r2_hidden(X27,X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.20/0.38  cnf(c_0_44, plain, (r2_hidden(X1,X3)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~v3_ordinal1(X3)|~r1_tarski(X1,X2)|~r2_hidden(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.38  cnf(c_0_45, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.38  cnf(c_0_46, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (v3_ordinal1(esk3_1(esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.38  cnf(c_0_48, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.38  cnf(c_0_49, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.38  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (v3_ordinal1(esk2_1(esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_42])).
% 0.20/0.38  cnf(c_0_52, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.38  fof(c_0_53, plain, ![X19, X20]:((~r2_hidden(X19,k1_ordinal1(X20))|(r2_hidden(X19,X20)|X19=X20))&((~r2_hidden(X19,X20)|r2_hidden(X19,k1_ordinal1(X20)))&(X19!=X20|r2_hidden(X19,k1_ordinal1(X20))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.20/0.38  cnf(c_0_54, plain, (r2_hidden(X1,X2)|~r1_tarski(X1,X3)|~r2_hidden(X3,X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)), inference(csr,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (v1_ordinal1(esk3_1(esk4_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.38  cnf(c_0_56, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (r1_tarski(X1,esk2_1(esk4_0))|~r1_ordinal1(X1,esk2_1(esk4_0))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (r1_ordinal1(X1,esk2_1(esk4_0))|r2_hidden(esk2_1(esk4_0),X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_52, c_0_51])).
% 0.20/0.38  cnf(c_0_59, plain, (r2_hidden(X1,k1_ordinal1(X2))|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(esk3_1(esk4_0),X1)|~r1_tarski(esk3_1(esk4_0),X2)|~r2_hidden(X2,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk2_1(esk4_0),k1_tarski(esk2_1(esk4_0))))), inference(spm,[status(thm)],[c_0_56, c_0_51])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (r1_tarski(esk3_1(esk4_0),esk2_1(esk4_0))|~r1_ordinal1(esk3_1(esk4_0),esk2_1(esk4_0))), inference(spm,[status(thm)],[c_0_57, c_0_47])).
% 0.20/0.38  cnf(c_0_63, negated_conjecture, (r1_ordinal1(esk3_1(esk4_0),esk2_1(esk4_0))|r2_hidden(esk2_1(esk4_0),esk3_1(esk4_0))), inference(spm,[status(thm)],[c_0_58, c_0_47])).
% 0.20/0.38  cnf(c_0_64, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|X1!=X2), inference(rw,[status(thm)],[c_0_59, c_0_49])).
% 0.20/0.38  cnf(c_0_65, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.38  cnf(c_0_66, negated_conjecture, (r2_hidden(esk3_1(esk4_0),k2_xboole_0(esk2_1(esk4_0),k1_tarski(esk2_1(esk4_0))))|~r1_tarski(esk3_1(esk4_0),X1)|~r2_hidden(X1,k2_xboole_0(esk2_1(esk4_0),k1_tarski(esk2_1(esk4_0))))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.38  cnf(c_0_67, negated_conjecture, (r1_tarski(esk3_1(esk4_0),esk2_1(esk4_0))|r2_hidden(esk2_1(esk4_0),esk3_1(esk4_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.38  cnf(c_0_68, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(er,[status(thm)],[c_0_64])).
% 0.20/0.38  cnf(c_0_69, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_65, c_0_49])).
% 0.20/0.38  cnf(c_0_70, negated_conjecture, (r2_hidden(esk3_1(esk4_0),k2_xboole_0(esk2_1(esk4_0),k1_tarski(esk2_1(esk4_0))))|r2_hidden(esk2_1(esk4_0),esk3_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])])).
% 0.20/0.38  cnf(c_0_71, plain, (v2_ordinal1(X1)|esk2_1(X1)!=esk3_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_72, negated_conjecture, (esk3_1(esk4_0)=esk2_1(esk4_0)|r2_hidden(esk2_1(esk4_0),esk3_1(esk4_0))|r2_hidden(esk3_1(esk4_0),esk2_1(esk4_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.38  cnf(c_0_73, plain, (v2_ordinal1(X1)|~r2_hidden(esk3_1(X1),esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_74, plain, (v2_ordinal1(X1)|~r2_hidden(esk2_1(X1),esk3_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_75, negated_conjecture, (v2_ordinal1(esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_74])).
% 0.20/0.38  cnf(c_0_76, negated_conjecture, (~v1_ordinal1(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_75]), c_0_23])).
% 0.20/0.38  cnf(c_0_77, negated_conjecture, (r2_hidden(esk1_1(esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_76, c_0_21])).
% 0.20/0.38  cnf(c_0_78, negated_conjecture, (r1_tarski(esk1_1(esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_77])).
% 0.20/0.38  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_78]), c_0_76]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 80
% 0.20/0.38  # Proof object clause steps            : 55
% 0.20/0.38  # Proof object formula steps           : 25
% 0.20/0.38  # Proof object conjectures             : 32
% 0.20/0.38  # Proof object clause conjectures      : 29
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 20
% 0.20/0.38  # Proof object initial formulas used   : 12
% 0.20/0.38  # Proof object generating inferences   : 30
% 0.20/0.38  # Proof object simplifying inferences  : 13
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 12
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 25
% 0.20/0.38  # Removed in clause preprocessing      : 1
% 0.20/0.38  # Initial clauses in saturation        : 24
% 0.20/0.38  # Processed clauses                    : 199
% 0.20/0.38  # ...of these trivial                  : 2
% 0.20/0.38  # ...subsumed                          : 16
% 0.20/0.38  # ...remaining for further processing  : 181
% 0.20/0.38  # Other redundant clauses eliminated   : 1
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 2
% 0.20/0.38  # Backward-rewritten                   : 15
% 0.20/0.38  # Generated clauses                    : 520
% 0.20/0.38  # ...of the previous two non-trivial   : 408
% 0.20/0.38  # Contextual simplify-reflections      : 5
% 0.20/0.38  # Paramodulations                      : 519
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 1
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 139
% 0.20/0.38  #    Positive orientable unit clauses  : 32
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 105
% 0.20/0.38  # Current number of unprocessed clauses: 228
% 0.20/0.38  # ...number of literals in the above   : 847
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 42
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 1075
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 529
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 21
% 0.20/0.38  # Unit Clause-clause subsumption calls : 298
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 8
% 0.20/0.38  # BW rewrite match successes           : 6
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 12148
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.038 s
% 0.20/0.38  # System time              : 0.007 s
% 0.20/0.38  # Total time               : 0.045 s
% 0.20/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
