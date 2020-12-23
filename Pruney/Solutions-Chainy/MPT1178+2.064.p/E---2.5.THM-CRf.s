%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:20 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 148 expanded)
%              Number of clauses        :   32 (  53 expanded)
%              Number of leaves         :   13 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :  172 ( 481 expanded)
%              Number of equality atoms :   31 ( 112 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t87_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(d17_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( X3 = k4_orders_2(X1,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X3)
                <=> m2_orders_2(X4,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

fof(t78_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => m2_orders_2(k1_tarski(k1_funct_1(X2,u1_struct_0(X1))),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_orders_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
           => k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t87_orders_2])).

fof(c_0_14,plain,(
    ! [X29,X30] :
      ( ~ r1_tarski(X29,X30)
      | r1_tarski(k3_tarski(X29),k3_tarski(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_orders_1(esk3_0,k1_orders_1(u1_struct_0(esk2_0)))
    & k3_tarski(k4_orders_2(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X28] : k3_tarski(k1_tarski(X28)) = X28 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X24,X25] : k2_enumset1(X24,X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_19,plain,(
    ! [X9,X10,X11,X12] : k3_enumset1(X9,X9,X10,X11,X12) = k2_enumset1(X9,X10,X11,X12) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_20,plain,(
    ! [X13,X14,X15,X16,X17] : k4_enumset1(X13,X13,X14,X15,X16,X17) = k3_enumset1(X13,X14,X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_21,plain,(
    ! [X18,X19,X20,X21,X22,X23] : k5_enumset1(X18,X18,X19,X20,X21,X22,X23) = k4_enumset1(X18,X19,X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

cnf(c_0_22,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X26,X27] :
      ( ( ~ r1_tarski(k1_tarski(X26),X27)
        | r2_hidden(X26,X27) )
      & ( ~ r2_hidden(X26,X27)
        | r1_tarski(k1_tarski(X26),X27) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_31,plain,(
    ! [X33,X34,X35,X36,X37,X38] :
      ( ( ~ r2_hidden(X36,X35)
        | m2_orders_2(X36,X33,X34)
        | X35 != k4_orders_2(X33,X34)
        | ~ m1_orders_1(X34,k1_orders_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v3_orders_2(X33)
        | ~ v4_orders_2(X33)
        | ~ v5_orders_2(X33)
        | ~ l1_orders_2(X33) )
      & ( ~ m2_orders_2(X37,X33,X34)
        | r2_hidden(X37,X35)
        | X35 != k4_orders_2(X33,X34)
        | ~ m1_orders_1(X34,k1_orders_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v3_orders_2(X33)
        | ~ v4_orders_2(X33)
        | ~ v5_orders_2(X33)
        | ~ l1_orders_2(X33) )
      & ( ~ r2_hidden(esk1_3(X33,X34,X38),X38)
        | ~ m2_orders_2(esk1_3(X33,X34,X38),X33,X34)
        | X38 = k4_orders_2(X33,X34)
        | ~ m1_orders_1(X34,k1_orders_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v3_orders_2(X33)
        | ~ v4_orders_2(X33)
        | ~ v5_orders_2(X33)
        | ~ l1_orders_2(X33) )
      & ( r2_hidden(esk1_3(X33,X34,X38),X38)
        | m2_orders_2(esk1_3(X33,X34,X38),X33,X34)
        | X38 = k4_orders_2(X33,X34)
        | ~ m1_orders_1(X34,k1_orders_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v3_orders_2(X33)
        | ~ v4_orders_2(X33)
        | ~ v5_orders_2(X33)
        | ~ l1_orders_2(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

fof(c_0_32,plain,(
    ! [X40,X41] :
      ( v2_struct_0(X40)
      | ~ v3_orders_2(X40)
      | ~ v4_orders_2(X40)
      | ~ v5_orders_2(X40)
      | ~ l1_orders_2(X40)
      | ~ m1_orders_1(X41,k1_orders_1(u1_struct_0(X40)))
      | m2_orders_2(k1_tarski(k1_funct_1(X41,u1_struct_0(X40))),X40,X41) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_orders_2])])])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k3_tarski(X1),k1_xboole_0)
    | ~ r1_tarski(X1,k4_orders_2(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_34,plain,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X4)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | X4 != k4_orders_2(X2,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( m1_orders_1(esk3_0,k1_orders_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | m2_orders_2(k1_tarski(k1_funct_1(X2,u1_struct_0(X1))),X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k4_orders_2(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_45,plain,
    ( r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k4_orders_2(esk2_0,esk3_0)
    | ~ m2_orders_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])]),c_0_42])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | m2_orders_2(k5_enumset1(k1_funct_1(X2,u1_struct_0(X1)),k1_funct_1(X2,u1_struct_0(X1)),k1_funct_1(X2,u1_struct_0(X1)),k1_funct_1(X2,u1_struct_0(X1)),k1_funct_1(X2,u1_struct_0(X1)),k1_funct_1(X2,u1_struct_0(X1)),k1_funct_1(X2,u1_struct_0(X1))),X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

fof(c_0_48,plain,(
    ! [X31,X32] :
      ( ~ r2_hidden(X31,X32)
      | ~ r1_tarski(X32,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_49,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ r2_hidden(X1,k4_orders_2(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k5_enumset1(k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0))),X1)
    | X1 != k4_orders_2(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])]),c_0_42])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k5_enumset1(k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n025.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 18:03:06 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.61/0.85  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_URBAN_S0Y
% 0.61/0.85  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.61/0.85  #
% 0.61/0.85  # Preprocessing time       : 0.028 s
% 0.61/0.85  
% 0.61/0.85  # Proof found!
% 0.61/0.85  # SZS status Theorem
% 0.61/0.85  # SZS output start CNFRefutation
% 0.61/0.85  fof(t87_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 0.61/0.85  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.61/0.85  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.61/0.85  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.61/0.85  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 0.61/0.85  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.61/0.85  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.61/0.85  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.61/0.85  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.61/0.85  fof(d17_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(X3=k4_orders_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>m2_orders_2(X4,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 0.61/0.85  fof(t78_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>m2_orders_2(k1_tarski(k1_funct_1(X2,u1_struct_0(X1))),X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_orders_2)).
% 0.61/0.85  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.61/0.85  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.61/0.85  fof(c_0_13, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t87_orders_2])).
% 0.61/0.85  fof(c_0_14, plain, ![X29, X30]:(~r1_tarski(X29,X30)|r1_tarski(k3_tarski(X29),k3_tarski(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.61/0.85  fof(c_0_15, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_orders_1(esk3_0,k1_orders_1(u1_struct_0(esk2_0)))&k3_tarski(k4_orders_2(esk2_0,esk3_0))=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.61/0.85  fof(c_0_16, plain, ![X28]:k3_tarski(k1_tarski(X28))=X28, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 0.61/0.85  fof(c_0_17, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.61/0.85  fof(c_0_18, plain, ![X24, X25]:k2_enumset1(X24,X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.61/0.85  fof(c_0_19, plain, ![X9, X10, X11, X12]:k3_enumset1(X9,X9,X10,X11,X12)=k2_enumset1(X9,X10,X11,X12), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.61/0.85  fof(c_0_20, plain, ![X13, X14, X15, X16, X17]:k4_enumset1(X13,X13,X14,X15,X16,X17)=k3_enumset1(X13,X14,X15,X16,X17), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.61/0.85  fof(c_0_21, plain, ![X18, X19, X20, X21, X22, X23]:k5_enumset1(X18,X18,X19,X20,X21,X22,X23)=k4_enumset1(X18,X19,X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.61/0.85  cnf(c_0_22, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.61/0.85  cnf(c_0_23, negated_conjecture, (k3_tarski(k4_orders_2(esk2_0,esk3_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.61/0.85  cnf(c_0_24, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.61/0.85  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.61/0.85  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.61/0.85  cnf(c_0_27, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.61/0.85  cnf(c_0_28, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.61/0.85  cnf(c_0_29, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.61/0.85  fof(c_0_30, plain, ![X26, X27]:((~r1_tarski(k1_tarski(X26),X27)|r2_hidden(X26,X27))&(~r2_hidden(X26,X27)|r1_tarski(k1_tarski(X26),X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.61/0.85  fof(c_0_31, plain, ![X33, X34, X35, X36, X37, X38]:(((~r2_hidden(X36,X35)|m2_orders_2(X36,X33,X34)|X35!=k4_orders_2(X33,X34)|~m1_orders_1(X34,k1_orders_1(u1_struct_0(X33)))|(v2_struct_0(X33)|~v3_orders_2(X33)|~v4_orders_2(X33)|~v5_orders_2(X33)|~l1_orders_2(X33)))&(~m2_orders_2(X37,X33,X34)|r2_hidden(X37,X35)|X35!=k4_orders_2(X33,X34)|~m1_orders_1(X34,k1_orders_1(u1_struct_0(X33)))|(v2_struct_0(X33)|~v3_orders_2(X33)|~v4_orders_2(X33)|~v5_orders_2(X33)|~l1_orders_2(X33))))&((~r2_hidden(esk1_3(X33,X34,X38),X38)|~m2_orders_2(esk1_3(X33,X34,X38),X33,X34)|X38=k4_orders_2(X33,X34)|~m1_orders_1(X34,k1_orders_1(u1_struct_0(X33)))|(v2_struct_0(X33)|~v3_orders_2(X33)|~v4_orders_2(X33)|~v5_orders_2(X33)|~l1_orders_2(X33)))&(r2_hidden(esk1_3(X33,X34,X38),X38)|m2_orders_2(esk1_3(X33,X34,X38),X33,X34)|X38=k4_orders_2(X33,X34)|~m1_orders_1(X34,k1_orders_1(u1_struct_0(X33)))|(v2_struct_0(X33)|~v3_orders_2(X33)|~v4_orders_2(X33)|~v5_orders_2(X33)|~l1_orders_2(X33))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).
% 0.61/0.85  fof(c_0_32, plain, ![X40, X41]:(v2_struct_0(X40)|~v3_orders_2(X40)|~v4_orders_2(X40)|~v5_orders_2(X40)|~l1_orders_2(X40)|(~m1_orders_1(X41,k1_orders_1(u1_struct_0(X40)))|m2_orders_2(k1_tarski(k1_funct_1(X41,u1_struct_0(X40))),X40,X41))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_orders_2])])])])).
% 0.61/0.85  cnf(c_0_33, negated_conjecture, (r1_tarski(k3_tarski(X1),k1_xboole_0)|~r1_tarski(X1,k4_orders_2(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.61/0.85  cnf(c_0_34, plain, (k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.61/0.85  cnf(c_0_35, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.61/0.85  cnf(c_0_36, plain, (r2_hidden(X1,X4)|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|X4!=k4_orders_2(X2,X3)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.61/0.85  cnf(c_0_37, negated_conjecture, (m1_orders_1(esk3_0,k1_orders_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.61/0.85  cnf(c_0_38, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.61/0.85  cnf(c_0_39, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.61/0.85  cnf(c_0_40, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.61/0.85  cnf(c_0_41, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.61/0.85  cnf(c_0_42, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.61/0.85  cnf(c_0_43, plain, (v2_struct_0(X1)|m2_orders_2(k1_tarski(k1_funct_1(X2,u1_struct_0(X1))),X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.61/0.85  cnf(c_0_44, negated_conjecture, (r1_tarski(X1,k1_xboole_0)|~r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k4_orders_2(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.61/0.85  cnf(c_0_45, plain, (r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.61/0.85  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,X2)|X2!=k4_orders_2(esk2_0,esk3_0)|~m2_orders_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])]), c_0_42])).
% 0.61/0.85  cnf(c_0_47, plain, (v2_struct_0(X1)|m2_orders_2(k5_enumset1(k1_funct_1(X2,u1_struct_0(X1)),k1_funct_1(X2,u1_struct_0(X1)),k1_funct_1(X2,u1_struct_0(X1)),k1_funct_1(X2,u1_struct_0(X1)),k1_funct_1(X2,u1_struct_0(X1)),k1_funct_1(X2,u1_struct_0(X1)),k1_funct_1(X2,u1_struct_0(X1))),X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.61/0.85  fof(c_0_48, plain, ![X31, X32]:(~r2_hidden(X31,X32)|~r1_tarski(X32,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.61/0.85  fof(c_0_49, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.61/0.85  cnf(c_0_50, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.61/0.85  cnf(c_0_51, negated_conjecture, (r1_tarski(X1,k1_xboole_0)|~r2_hidden(X1,k4_orders_2(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.61/0.85  cnf(c_0_52, negated_conjecture, (r2_hidden(k5_enumset1(k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0))),X1)|X1!=k4_orders_2(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])]), c_0_42])).
% 0.61/0.85  cnf(c_0_53, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.61/0.85  cnf(c_0_54, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.61/0.85  cnf(c_0_55, plain, (r2_hidden(X1,X2)|~r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.61/0.85  cnf(c_0_56, negated_conjecture, (r1_tarski(k5_enumset1(k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0)),k1_funct_1(esk3_0,u1_struct_0(esk2_0))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.61/0.85  cnf(c_0_57, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.61/0.85  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), ['proof']).
% 0.61/0.85  # SZS output end CNFRefutation
% 0.61/0.85  # Proof object total steps             : 59
% 0.61/0.85  # Proof object clause steps            : 32
% 0.61/0.85  # Proof object formula steps           : 27
% 0.61/0.85  # Proof object conjectures             : 17
% 0.61/0.85  # Proof object clause conjectures      : 14
% 0.61/0.85  # Proof object formula conjectures     : 3
% 0.61/0.85  # Proof object initial clauses used    : 20
% 0.61/0.85  # Proof object initial formulas used   : 13
% 0.61/0.85  # Proof object generating inferences   : 8
% 0.61/0.85  # Proof object simplifying inferences  : 34
% 0.61/0.85  # Training examples: 0 positive, 0 negative
% 0.61/0.85  # Parsed axioms                        : 13
% 0.61/0.85  # Removed by relevancy pruning/SinE    : 0
% 0.61/0.85  # Initial clauses                      : 23
% 0.61/0.85  # Removed in clause preprocessing      : 5
% 0.61/0.85  # Initial clauses in saturation        : 18
% 0.61/0.85  # Processed clauses                    : 639
% 0.61/0.85  # ...of these trivial                  : 0
% 0.61/0.85  # ...subsumed                          : 9
% 0.61/0.85  # ...remaining for further processing  : 630
% 0.61/0.85  # Other redundant clauses eliminated   : 0
% 0.61/0.85  # Clauses deleted for lack of memory   : 0
% 0.61/0.85  # Backward-subsumed                    : 0
% 0.61/0.85  # Backward-rewritten                   : 0
% 0.61/0.85  # Generated clauses                    : 1305
% 0.61/0.85  # ...of the previous two non-trivial   : 1300
% 0.61/0.85  # Contextual simplify-reflections      : 0
% 0.61/0.85  # Paramodulations                      : 1305
% 0.61/0.85  # Factorizations                       : 0
% 0.61/0.85  # Equation resolutions                 : 0
% 0.61/0.85  # Propositional unsat checks           : 0
% 0.61/0.85  #    Propositional check models        : 0
% 0.61/0.85  #    Propositional check unsatisfiable : 0
% 0.61/0.85  #    Propositional clauses             : 0
% 0.61/0.85  #    Propositional clauses after purity: 0
% 0.61/0.85  #    Propositional unsat core size     : 0
% 0.61/0.85  #    Propositional preprocessing time  : 0.000
% 0.61/0.85  #    Propositional encoding time       : 0.000
% 0.61/0.85  #    Propositional solver time         : 0.000
% 0.61/0.85  #    Success case prop preproc time    : 0.000
% 0.61/0.85  #    Success case prop encoding time   : 0.000
% 0.61/0.85  #    Success case prop solver time     : 0.000
% 0.61/0.85  # Current number of processed clauses  : 630
% 0.61/0.85  #    Positive orientable unit clauses  : 415
% 0.61/0.85  #    Positive unorientable unit clauses: 0
% 0.61/0.85  #    Negative unit clauses             : 192
% 0.61/0.85  #    Non-unit-clauses                  : 23
% 0.61/0.85  # Current number of unprocessed clauses: 678
% 0.61/0.85  # ...number of literals in the above   : 689
% 0.61/0.85  # Current number of archived formulas  : 0
% 0.61/0.85  # Current number of archived clauses   : 5
% 0.61/0.85  # Clause-clause subsumption calls (NU) : 242
% 0.61/0.85  # Rec. Clause-clause subsumption calls : 68
% 0.61/0.85  # Non-unit clause-clause subsumptions  : 3
% 0.61/0.85  # Unit Clause-clause subsumption calls : 16905
% 0.61/0.85  # Rewrite failures with RHS unbound    : 0
% 0.61/0.85  # BW rewrite match attempts            : 81810
% 0.61/0.85  # BW rewrite match successes           : 0
% 0.61/0.85  # Condensation attempts                : 0
% 0.61/0.85  # Condensation successes               : 0
% 0.61/0.85  # Termbank termtop insertions          : 343282
% 0.61/0.85  
% 0.61/0.85  # -------------------------------------------------
% 0.61/0.85  # User time                : 0.519 s
% 0.61/0.85  # System time              : 0.017 s
% 0.61/0.85  # Total time               : 0.536 s
% 0.61/0.85  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
