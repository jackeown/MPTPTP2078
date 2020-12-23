%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:14 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 565 expanded)
%              Number of clauses        :   48 ( 203 expanded)
%              Number of leaves         :   15 ( 140 expanded)
%              Depth                    :   13
%              Number of atoms          :  266 (2790 expanded)
%              Number of equality atoms :   54 ( 465 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t79_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m2_orders_2(X3,X1,X2)
             => r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(fc9_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) )
     => ~ v1_xboole_0(k4_orders_2(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

fof(c_0_15,plain,(
    ! [X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X29,X28)
        | m2_orders_2(X29,X26,X27)
        | X28 != k4_orders_2(X26,X27)
        | ~ m1_orders_1(X27,k1_orders_1(u1_struct_0(X26)))
        | v2_struct_0(X26)
        | ~ v3_orders_2(X26)
        | ~ v4_orders_2(X26)
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26) )
      & ( ~ m2_orders_2(X30,X26,X27)
        | r2_hidden(X30,X28)
        | X28 != k4_orders_2(X26,X27)
        | ~ m1_orders_1(X27,k1_orders_1(u1_struct_0(X26)))
        | v2_struct_0(X26)
        | ~ v3_orders_2(X26)
        | ~ v4_orders_2(X26)
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26) )
      & ( ~ r2_hidden(esk2_3(X26,X27,X31),X31)
        | ~ m2_orders_2(esk2_3(X26,X27,X31),X26,X27)
        | X31 = k4_orders_2(X26,X27)
        | ~ m1_orders_1(X27,k1_orders_1(u1_struct_0(X26)))
        | v2_struct_0(X26)
        | ~ v3_orders_2(X26)
        | ~ v4_orders_2(X26)
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26) )
      & ( r2_hidden(esk2_3(X26,X27,X31),X31)
        | m2_orders_2(esk2_3(X26,X27,X31),X26,X27)
        | X31 = k4_orders_2(X26,X27)
        | ~ m1_orders_1(X27,k1_orders_1(u1_struct_0(X26)))
        | v2_struct_0(X26)
        | ~ v3_orders_2(X26)
        | ~ v4_orders_2(X26)
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

fof(c_0_16,negated_conjecture,(
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

cnf(c_0_17,plain,
    ( r2_hidden(X1,X4)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | X4 != k4_orders_2(X2,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v4_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk3_0)))
    & k3_tarski(k4_orders_2(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k4_orders_2(X1,X3))
    | ~ m2_orders_2(X2,X1,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | m2_orders_2(esk2_3(X1,X2,X3),X1,X2)
    | X3 = k4_orders_2(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_27,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | m1_subset_1(k1_tarski(X22),k1_zfmisc_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

fof(c_0_28,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_29,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_30,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,k4_orders_2(esk3_0,esk4_0))
    | ~ m2_orders_2(X1,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( X1 = k4_orders_2(esk3_0,esk4_0)
    | m2_orders_2(esk2_3(esk3_0,esk4_0,X1),esk3_0,esk4_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

fof(c_0_33,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_34,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | r1_tarski(k3_tarski(X20),k3_tarski(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

fof(c_0_35,plain,(
    ! [X19] : k3_tarski(k1_tarski(X19)) = X19 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

fof(c_0_36,plain,(
    ! [X24,X25] :
      ( ( ~ m1_subset_1(X24,k1_zfmisc_1(X25))
        | r1_tarski(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | m1_subset_1(X24,k1_zfmisc_1(X25)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_37,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( X1 = k4_orders_2(esk3_0,esk4_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,X1),k4_orders_2(esk3_0,esk4_0))
    | r2_hidden(esk2_3(esk3_0,esk4_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( X1 = k4_orders_2(esk3_0,esk4_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,X1),k4_orders_2(esk3_0,esk4_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_49,plain,(
    ! [X15,X16] :
      ( ( k2_zfmisc_1(X15,X16) != k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_50,plain,
    ( k3_tarski(X1) = k3_tarski(X2)
    | ~ r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_38]),c_0_39])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_enumset1(X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( X1 = k4_orders_2(esk3_0,esk4_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,X1),k4_orders_2(esk3_0,esk4_0))
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_54,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_55,plain,(
    ! [X35,X36,X37] :
      ( v2_struct_0(X35)
      | ~ v3_orders_2(X35)
      | ~ v4_orders_2(X35)
      | ~ v5_orders_2(X35)
      | ~ l1_orders_2(X35)
      | ~ m1_orders_1(X36,k1_orders_1(u1_struct_0(X35)))
      | ~ m2_orders_2(X37,X35,X36)
      | r2_hidden(k1_funct_1(X36,u1_struct_0(X35)),X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_orders_2])])])])).

fof(c_0_56,plain,(
    ! [X17,X18] : ~ r2_hidden(X17,k2_zfmisc_1(X17,X18)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_58,plain,(
    ! [X33,X34] :
      ( v2_struct_0(X33)
      | ~ v3_orders_2(X33)
      | ~ v4_orders_2(X33)
      | ~ v5_orders_2(X33)
      | ~ l1_orders_2(X33)
      | ~ m1_orders_1(X34,k1_orders_1(u1_struct_0(X33)))
      | ~ v1_xboole_0(k4_orders_2(X33,X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_orders_2])])])).

cnf(c_0_59,plain,
    ( k3_tarski(X1) = X2
    | ~ r1_tarski(k1_enumset1(X2,X2,X2),X1)
    | ~ r1_tarski(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( X1 = k4_orders_2(esk3_0,esk4_0)
    | r1_tarski(k1_enumset1(esk2_3(esk3_0,esk4_0,X1),esk2_3(esk3_0,esk4_0,X1),esk2_3(esk3_0,esk4_0,X1)),k4_orders_2(esk3_0,esk4_0))
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( X1 = k4_orders_2(esk3_0,esk4_0)
    | r2_hidden(esk1_1(X1),X1)
    | ~ v1_xboole_0(k4_orders_2(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_53])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m2_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(k4_orders_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( k1_xboole_0 = esk2_3(esk3_0,esk4_0,X1)
    | X1 = k4_orders_2(esk3_0,esk4_0)
    | r2_hidden(esk1_1(X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_61]),c_0_62])])).

cnf(c_0_69,negated_conjecture,
    ( X1 = k4_orders_2(esk3_0,esk4_0)
    | r2_hidden(esk1_1(k4_orders_2(esk3_0,esk4_0)),k4_orders_2(esk3_0,esk4_0))
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_48])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,u1_struct_0(esk3_0)),X1)
    | ~ m2_orders_2(X1,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( k1_xboole_0 = esk2_3(esk3_0,esk4_0,X1)
    | r2_hidden(esk1_1(X1),X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25]),c_0_48])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk1_1(k4_orders_2(esk3_0,esk4_0)),k4_orders_2(esk3_0,esk4_0))
    | r2_hidden(esk1_1(X1),X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_69]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25]),c_0_48])).

cnf(c_0_74,negated_conjecture,
    ( X1 = k4_orders_2(esk3_0,esk4_0)
    | r2_hidden(k1_funct_1(esk4_0,u1_struct_0(esk3_0)),esk2_3(esk3_0,esk4_0,X1))
    | r2_hidden(esk2_3(esk3_0,esk4_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_32])).

cnf(c_0_75,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk1_1(k4_orders_2(esk3_0,esk4_0)),k4_orders_2(esk3_0,esk4_0)) ),
    inference(ef,[status(thm)],[c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( k4_orders_2(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_71]),c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77]),c_0_77]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.028 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(d17_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(X3=k4_orders_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>m2_orders_2(X4,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 0.13/0.40  fof(t87_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 0.13/0.40  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 0.13/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.40  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.13/0.40  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.13/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.40  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.40  fof(t79_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 0.13/0.40  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.13/0.40  fof(fc9_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>~(v1_xboole_0(k4_orders_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 0.13/0.40  fof(c_0_15, plain, ![X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X29,X28)|m2_orders_2(X29,X26,X27)|X28!=k4_orders_2(X26,X27)|~m1_orders_1(X27,k1_orders_1(u1_struct_0(X26)))|(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)))&(~m2_orders_2(X30,X26,X27)|r2_hidden(X30,X28)|X28!=k4_orders_2(X26,X27)|~m1_orders_1(X27,k1_orders_1(u1_struct_0(X26)))|(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26))))&((~r2_hidden(esk2_3(X26,X27,X31),X31)|~m2_orders_2(esk2_3(X26,X27,X31),X26,X27)|X31=k4_orders_2(X26,X27)|~m1_orders_1(X27,k1_orders_1(u1_struct_0(X26)))|(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)))&(r2_hidden(esk2_3(X26,X27,X31),X31)|m2_orders_2(esk2_3(X26,X27,X31),X26,X27)|X31=k4_orders_2(X26,X27)|~m1_orders_1(X27,k1_orders_1(u1_struct_0(X26)))|(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).
% 0.13/0.40  fof(c_0_16, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t87_orders_2])).
% 0.13/0.40  cnf(c_0_17, plain, (r2_hidden(X1,X4)|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|X4!=k4_orders_2(X2,X3)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  fof(c_0_18, negated_conjecture, (((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&v5_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk3_0)))&k3_tarski(k4_orders_2(esk3_0,esk4_0))=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.13/0.40  cnf(c_0_19, plain, (v2_struct_0(X1)|r2_hidden(X2,k4_orders_2(X1,X3))|~m2_orders_2(X2,X1,X3)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_20, negated_conjecture, (m1_orders_1(esk4_0,k1_orders_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_21, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_22, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_23, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_24, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_26, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|m2_orders_2(esk2_3(X1,X2,X3),X1,X2)|X3=k4_orders_2(X1,X2)|v2_struct_0(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  fof(c_0_27, plain, ![X22, X23]:(~r2_hidden(X22,X23)|m1_subset_1(k1_tarski(X22),k1_zfmisc_1(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.13/0.40  fof(c_0_28, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.40  fof(c_0_29, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.40  fof(c_0_30, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.40  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,k4_orders_2(esk3_0,esk4_0))|~m2_orders_2(X1,esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.13/0.40  cnf(c_0_32, negated_conjecture, (X1=k4_orders_2(esk3_0,esk4_0)|m2_orders_2(esk2_3(esk3_0,esk4_0,X1),esk3_0,esk4_0)|r2_hidden(esk2_3(esk3_0,esk4_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.13/0.40  fof(c_0_33, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.40  fof(c_0_34, plain, ![X20, X21]:(~r1_tarski(X20,X21)|r1_tarski(k3_tarski(X20),k3_tarski(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.13/0.40  fof(c_0_35, plain, ![X19]:k3_tarski(k1_tarski(X19))=X19, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 0.13/0.40  fof(c_0_36, plain, ![X24, X25]:((~m1_subset_1(X24,k1_zfmisc_1(X25))|r1_tarski(X24,X25))&(~r1_tarski(X24,X25)|m1_subset_1(X24,k1_zfmisc_1(X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.40  cnf(c_0_37, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.40  cnf(c_0_38, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.40  cnf(c_0_39, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.40  cnf(c_0_40, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (X1=k4_orders_2(esk3_0,esk4_0)|r2_hidden(esk2_3(esk3_0,esk4_0,X1),k4_orders_2(esk3_0,esk4_0))|r2_hidden(esk2_3(esk3_0,esk4_0,X1),X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.40  cnf(c_0_42, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.40  cnf(c_0_43, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.40  cnf(c_0_44, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.40  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.40  cnf(c_0_46, plain, (m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.13/0.40  cnf(c_0_47, negated_conjecture, (X1=k4_orders_2(esk3_0,esk4_0)|r2_hidden(esk2_3(esk3_0,esk4_0,X1),k4_orders_2(esk3_0,esk4_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.40  cnf(c_0_48, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.40  fof(c_0_49, plain, ![X15, X16]:((k2_zfmisc_1(X15,X16)!=k1_xboole_0|(X15=k1_xboole_0|X16=k1_xboole_0))&((X15!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0)&(X16!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.13/0.40  cnf(c_0_50, plain, (k3_tarski(X1)=k3_tarski(X2)|~r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.40  cnf(c_0_51, plain, (k3_tarski(k1_enumset1(X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_38]), c_0_39])).
% 0.13/0.40  cnf(c_0_52, plain, (r1_tarski(k1_enumset1(X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (X1=k4_orders_2(esk3_0,esk4_0)|r2_hidden(esk2_3(esk3_0,esk4_0,X1),k4_orders_2(esk3_0,esk4_0))|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.40  fof(c_0_54, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.40  fof(c_0_55, plain, ![X35, X36, X37]:(v2_struct_0(X35)|~v3_orders_2(X35)|~v4_orders_2(X35)|~v5_orders_2(X35)|~l1_orders_2(X35)|(~m1_orders_1(X36,k1_orders_1(u1_struct_0(X35)))|(~m2_orders_2(X37,X35,X36)|r2_hidden(k1_funct_1(X36,u1_struct_0(X35)),X37)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_orders_2])])])])).
% 0.13/0.40  fof(c_0_56, plain, ![X17, X18]:~r2_hidden(X17,k2_zfmisc_1(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.13/0.40  cnf(c_0_57, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.40  fof(c_0_58, plain, ![X33, X34]:(v2_struct_0(X33)|~v3_orders_2(X33)|~v4_orders_2(X33)|~v5_orders_2(X33)|~l1_orders_2(X33)|~m1_orders_1(X34,k1_orders_1(u1_struct_0(X33)))|~v1_xboole_0(k4_orders_2(X33,X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_orders_2])])])).
% 0.13/0.40  cnf(c_0_59, plain, (k3_tarski(X1)=X2|~r1_tarski(k1_enumset1(X2,X2,X2),X1)|~r1_tarski(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.40  cnf(c_0_60, negated_conjecture, (X1=k4_orders_2(esk3_0,esk4_0)|r1_tarski(k1_enumset1(esk2_3(esk3_0,esk4_0,X1),esk2_3(esk3_0,esk4_0,X1),esk2_3(esk3_0,esk4_0,X1)),k4_orders_2(esk3_0,esk4_0))|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.40  cnf(c_0_61, negated_conjecture, (k3_tarski(k4_orders_2(esk3_0,esk4_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_62, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.40  cnf(c_0_63, negated_conjecture, (X1=k4_orders_2(esk3_0,esk4_0)|r2_hidden(esk1_1(X1),X1)|~v1_xboole_0(k4_orders_2(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_53])).
% 0.13/0.40  cnf(c_0_64, plain, (v2_struct_0(X1)|r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~m2_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.13/0.40  cnf(c_0_65, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.13/0.40  cnf(c_0_66, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_57])).
% 0.13/0.40  cnf(c_0_67, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~v1_xboole_0(k4_orders_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.40  cnf(c_0_68, negated_conjecture, (k1_xboole_0=esk2_3(esk3_0,esk4_0,X1)|X1=k4_orders_2(esk3_0,esk4_0)|r2_hidden(esk1_1(X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_61]), c_0_62])])).
% 0.13/0.40  cnf(c_0_69, negated_conjecture, (X1=k4_orders_2(esk3_0,esk4_0)|r2_hidden(esk1_1(k4_orders_2(esk3_0,esk4_0)),k4_orders_2(esk3_0,esk4_0))|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_63, c_0_48])).
% 0.13/0.40  cnf(c_0_70, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,u1_struct_0(esk3_0)),X1)|~m2_orders_2(X1,esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.13/0.40  cnf(c_0_71, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.13/0.40  cnf(c_0_72, negated_conjecture, (k1_xboole_0=esk2_3(esk3_0,esk4_0,X1)|r2_hidden(esk1_1(X1),X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25]), c_0_48])).
% 0.13/0.40  cnf(c_0_73, negated_conjecture, (r2_hidden(esk1_1(k4_orders_2(esk3_0,esk4_0)),k4_orders_2(esk3_0,esk4_0))|r2_hidden(esk1_1(X1),X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_69]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25]), c_0_48])).
% 0.13/0.40  cnf(c_0_74, negated_conjecture, (X1=k4_orders_2(esk3_0,esk4_0)|r2_hidden(k1_funct_1(esk4_0,u1_struct_0(esk3_0)),esk2_3(esk3_0,esk4_0,X1))|r2_hidden(esk2_3(esk3_0,esk4_0,X1),X1)), inference(spm,[status(thm)],[c_0_70, c_0_32])).
% 0.13/0.40  cnf(c_0_75, negated_conjecture, (esk2_3(esk3_0,esk4_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.13/0.40  cnf(c_0_76, negated_conjecture, (r2_hidden(esk1_1(k4_orders_2(esk3_0,esk4_0)),k4_orders_2(esk3_0,esk4_0))), inference(ef,[status(thm)],[c_0_73])).
% 0.13/0.40  cnf(c_0_77, negated_conjecture, (k4_orders_2(esk3_0,esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_71]), c_0_71])).
% 0.13/0.40  cnf(c_0_78, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77]), c_0_77]), c_0_71]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 79
% 0.13/0.40  # Proof object clause steps            : 48
% 0.13/0.40  # Proof object formula steps           : 31
% 0.13/0.40  # Proof object conjectures             : 27
% 0.13/0.40  # Proof object clause conjectures      : 24
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 23
% 0.13/0.40  # Proof object initial formulas used   : 15
% 0.13/0.40  # Proof object generating inferences   : 20
% 0.13/0.40  # Proof object simplifying inferences  : 49
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 15
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 30
% 0.13/0.40  # Removed in clause preprocessing      : 2
% 0.13/0.40  # Initial clauses in saturation        : 28
% 0.13/0.40  # Processed clauses                    : 299
% 0.13/0.40  # ...of these trivial                  : 2
% 0.13/0.40  # ...subsumed                          : 114
% 0.13/0.40  # ...remaining for further processing  : 183
% 0.13/0.40  # Other redundant clauses eliminated   : 6
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 8
% 0.13/0.40  # Backward-rewritten                   : 80
% 0.13/0.40  # Generated clauses                    : 986
% 0.13/0.40  # ...of the previous two non-trivial   : 813
% 0.13/0.40  # Contextual simplify-reflections      : 2
% 0.13/0.40  # Paramodulations                      : 974
% 0.13/0.40  # Factorizations                       : 6
% 0.13/0.40  # Equation resolutions                 : 6
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 62
% 0.13/0.40  #    Positive orientable unit clauses  : 13
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 3
% 0.13/0.40  #    Non-unit-clauses                  : 46
% 0.13/0.40  # Current number of unprocessed clauses: 524
% 0.13/0.40  # ...number of literals in the above   : 2306
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 117
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 2896
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 1675
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 115
% 0.13/0.40  # Unit Clause-clause subsumption calls : 28
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 9
% 0.13/0.40  # BW rewrite match successes           : 4
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 21349
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.054 s
% 0.13/0.40  # System time              : 0.004 s
% 0.13/0.40  # Total time               : 0.059 s
% 0.13/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
