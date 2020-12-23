%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:23 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 654 expanded)
%              Number of clauses        :   88 ( 318 expanded)
%              Number of leaves         :   16 ( 161 expanded)
%              Depth                    :   20
%              Number of atoms          :  307 (2049 expanded)
%              Number of equality atoms :   39 ( 283 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

fof(c_0_17,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(X24,X25)
      | ~ r1_tarski(X25,X26)
      | r1_tarski(X24,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k3_relat_1(esk3_0),k3_relat_1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_19,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | k2_xboole_0(X22,X23) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_20,plain,(
    ! [X39,X40] : k3_tarski(k2_tarski(X39,X40)) = k2_xboole_0(X39,X40) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X27,X28] : r1_tarski(k4_xboole_0(X27,X28),X27) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_24,plain,(
    ! [X29,X30,X31] :
      ( ~ r1_tarski(k4_xboole_0(X29,X30),X31)
      | r1_tarski(X29,k2_xboole_0(X30,X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X37,X38] : k2_tarski(X37,X38) = k2_tarski(X38,X37) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_35,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,k4_xboole_0(esk3_0,X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_33])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(esk3_0,X1),X2),esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_29])).

fof(c_0_39,plain,(
    ! [X32,X33] : r1_tarski(X32,k2_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_40,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,X1),X2)
    | ~ r1_tarski(esk4_0,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_43,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_44,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_tarski(esk4_0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_41])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_26])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_49,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X43)
      | ~ m1_subset_1(X44,k1_zfmisc_1(X43))
      | v1_relat_1(X44) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_50,plain,(
    ! [X41,X42] :
      ( ( ~ m1_subset_1(X41,k1_zfmisc_1(X42))
        | r1_tarski(X41,X42) )
      & ( ~ r1_tarski(X41,X42)
        | m1_subset_1(X41,k1_zfmisc_1(X42)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_tarski(k3_tarski(k2_tarski(esk4_0,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_58,plain,(
    ! [X46,X47] :
      ( ( r1_tarski(k1_relat_1(X46),k1_relat_1(X47))
        | ~ r1_tarski(X46,X47)
        | ~ v1_relat_1(X47)
        | ~ v1_relat_1(X46) )
      & ( r1_tarski(k2_relat_1(X46),k2_relat_1(X47))
        | ~ r1_tarski(X46,X47)
        | ~ v1_relat_1(X47)
        | ~ v1_relat_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_59,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X3)
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk3_0,k3_tarski(k2_tarski(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_57])).

fof(c_0_66,plain,(
    ! [X45] :
      ( ~ v1_relat_1(X45)
      | k3_relat_1(X45) = k2_xboole_0(k1_relat_1(X45),k2_relat_1(X45)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_67,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X1))
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_54])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),k3_tarski(k2_tarski(esk4_0,X2)))
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,plain,
    ( r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X2)
    | r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_65,c_0_54])).

cnf(c_0_73,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_74,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_75,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,plain,
    ( r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_69,c_0_54])).

cnf(c_0_77,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(k3_tarski(k2_tarski(esk4_0,X1)),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_79,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_72])).

cnf(c_0_80,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[c_0_73,c_0_68])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_32])).

cnf(c_0_82,plain,
    ( k3_relat_1(X1) = k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_74,c_0_26])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_75])).

cnf(c_0_84,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))
    | ~ r2_hidden(esk1_2(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1)),X3) ),
    inference(spm,[status(thm)],[c_0_62,c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( k3_xboole_0(k3_tarski(k2_tarski(esk4_0,X1)),esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])])).

cnf(c_0_86,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_76])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_80])).

cnf(c_0_88,plain,
    ( r1_tarski(k2_relat_1(X1),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_89,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_75]),c_0_68])).

cnf(c_0_90,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_91,plain,
    ( k2_relat_1(X1) = k2_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_75])).

cnf(c_0_92,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_72])).

cnf(c_0_93,negated_conjecture,
    ( k3_xboole_0(X1,esk3_0) = esk3_0
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_31])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_86])).

cnf(c_0_95,plain,
    ( r1_tarski(k1_relat_1(X1),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_82])).

cnf(c_0_96,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_80]),c_0_68])).

cnf(c_0_97,plain,
    ( k1_relat_1(X1) = k1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_80])).

fof(c_0_98,plain,(
    ! [X34,X35,X36] :
      ( ~ r1_tarski(X34,X35)
      | ~ r1_tarski(X36,X35)
      | r1_tarski(k2_xboole_0(X34,X36),X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_99,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_88])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(esk4_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_22]),c_0_90])])).

cnf(c_0_101,plain,
    ( k2_relat_1(X1) = k2_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_75]),c_0_68])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(esk3_0,X1))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_103,negated_conjecture,
    ( v1_relat_1(k3_xboole_0(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_94]),c_0_90])])).

cnf(c_0_104,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_95])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(esk4_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_22]),c_0_90])])).

cnf(c_0_106,plain,
    ( k1_relat_1(X1) = k1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_80]),c_0_68])).

cnf(c_0_107,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),k3_relat_1(esk4_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_90])])).

cnf(c_0_109,negated_conjecture,
    ( k2_relat_1(k3_xboole_0(esk3_0,X1)) = k2_relat_1(esk3_0)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103]),c_0_86])])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(k1_relat_1(X1),k3_relat_1(esk4_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_90])])).

cnf(c_0_111,negated_conjecture,
    ( k1_relat_1(k3_xboole_0(esk3_0,X1)) = k1_relat_1(esk3_0)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_102]),c_0_103]),c_0_86])])).

cnf(c_0_112,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_107,c_0_26])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),k3_relat_1(esk4_0))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_86])])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),k3_relat_1(esk4_0))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_86])])).

cnf(c_0_115,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_112,c_0_82])).

cnf(c_0_116,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),k3_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_47])).

cnf(c_0_117,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),k3_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_47])).

cnf(c_0_119,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk3_0),k3_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_120,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117]),c_0_118])]),c_0_119]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.78/0.94  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.78/0.94  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.78/0.94  #
% 0.78/0.94  # Preprocessing time       : 0.029 s
% 0.78/0.94  # Presaturation interreduction done
% 0.78/0.94  
% 0.78/0.94  # Proof found!
% 0.78/0.94  # SZS status Theorem
% 0.78/0.94  # SZS output start CNFRefutation
% 0.78/0.94  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 0.78/0.94  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.78/0.94  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.78/0.94  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.78/0.94  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.78/0.94  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.78/0.94  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.78/0.94  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.78/0.94  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.78/0.94  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.78/0.94  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.78/0.94  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.78/0.94  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.78/0.94  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.78/0.94  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 0.78/0.94  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.78/0.94  fof(c_0_16, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 0.78/0.94  fof(c_0_17, plain, ![X24, X25, X26]:(~r1_tarski(X24,X25)|~r1_tarski(X25,X26)|r1_tarski(X24,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.78/0.94  fof(c_0_18, negated_conjecture, (v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&(r1_tarski(esk3_0,esk4_0)&~r1_tarski(k3_relat_1(esk3_0),k3_relat_1(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.78/0.94  fof(c_0_19, plain, ![X22, X23]:(~r1_tarski(X22,X23)|k2_xboole_0(X22,X23)=X23), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.78/0.94  fof(c_0_20, plain, ![X39, X40]:k3_tarski(k2_tarski(X39,X40))=k2_xboole_0(X39,X40), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.78/0.94  cnf(c_0_21, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.78/0.94  cnf(c_0_22, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.78/0.94  fof(c_0_23, plain, ![X27, X28]:r1_tarski(k4_xboole_0(X27,X28),X27), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.78/0.94  fof(c_0_24, plain, ![X29, X30, X31]:(~r1_tarski(k4_xboole_0(X29,X30),X31)|r1_tarski(X29,k2_xboole_0(X30,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.78/0.94  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.78/0.94  cnf(c_0_26, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.78/0.94  fof(c_0_27, plain, ![X37, X38]:k2_tarski(X37,X38)=k2_tarski(X38,X37), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.78/0.94  cnf(c_0_28, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.78/0.94  cnf(c_0_29, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.78/0.94  cnf(c_0_30, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.78/0.94  cnf(c_0_31, plain, (k3_tarski(k2_tarski(X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.78/0.94  cnf(c_0_32, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.78/0.94  cnf(c_0_33, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.78/0.94  cnf(c_0_34, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_30, c_0_26])).
% 0.78/0.94  cnf(c_0_35, plain, (k3_tarski(k2_tarski(X1,X2))=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.78/0.94  cnf(c_0_36, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,k4_xboole_0(esk3_0,X2))), inference(spm,[status(thm)],[c_0_21, c_0_33])).
% 0.78/0.94  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.78/0.94  cnf(c_0_38, negated_conjecture, (r1_tarski(k4_xboole_0(k4_xboole_0(esk3_0,X1),X2),esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_29])).
% 0.78/0.94  fof(c_0_39, plain, ![X32, X33]:r1_tarski(X32,k2_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.78/0.94  fof(c_0_40, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.78/0.94  cnf(c_0_41, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,X1),X2)|~r1_tarski(esk4_0,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.78/0.94  cnf(c_0_42, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.78/0.94  fof(c_0_43, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.78/0.94  fof(c_0_44, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.78/0.94  cnf(c_0_45, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.78/0.94  cnf(c_0_46, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_tarski(esk4_0,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_37, c_0_41])).
% 0.78/0.94  cnf(c_0_47, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_42, c_0_26])).
% 0.78/0.94  cnf(c_0_48, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.78/0.94  fof(c_0_49, plain, ![X43, X44]:(~v1_relat_1(X43)|(~m1_subset_1(X44,k1_zfmisc_1(X43))|v1_relat_1(X44))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.78/0.94  fof(c_0_50, plain, ![X41, X42]:((~m1_subset_1(X41,k1_zfmisc_1(X42))|r1_tarski(X41,X42))&(~r1_tarski(X41,X42)|m1_subset_1(X41,k1_zfmisc_1(X42)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.78/0.94  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.78/0.94  cnf(c_0_52, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_45])).
% 0.78/0.94  cnf(c_0_53, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.78/0.94  cnf(c_0_54, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.78/0.94  cnf(c_0_55, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_tarski(k3_tarski(k2_tarski(esk4_0,X2)),X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.78/0.94  cnf(c_0_56, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_48])).
% 0.78/0.94  cnf(c_0_57, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.78/0.94  fof(c_0_58, plain, ![X46, X47]:((r1_tarski(k1_relat_1(X46),k1_relat_1(X47))|~r1_tarski(X46,X47)|~v1_relat_1(X47)|~v1_relat_1(X46))&(r1_tarski(k2_relat_1(X46),k2_relat_1(X47))|~r1_tarski(X46,X47)|~v1_relat_1(X47)|~v1_relat_1(X46))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.78/0.94  cnf(c_0_59, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.78/0.94  cnf(c_0_60, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.78/0.94  cnf(c_0_61, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.78/0.94  cnf(c_0_62, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X3)|~r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.78/0.94  cnf(c_0_63, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.78/0.94  cnf(c_0_64, negated_conjecture, (r1_tarski(esk3_0,k3_tarski(k2_tarski(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.78/0.94  cnf(c_0_65, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_57])).
% 0.78/0.94  fof(c_0_66, plain, ![X45]:(~v1_relat_1(X45)|k3_relat_1(X45)=k2_xboole_0(k1_relat_1(X45),k2_relat_1(X45))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.78/0.94  cnf(c_0_67, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.78/0.94  cnf(c_0_68, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.78/0.94  cnf(c_0_69, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_61])).
% 0.78/0.94  cnf(c_0_70, plain, (r1_tarski(X1,k3_xboole_0(X2,X1))|~r2_hidden(esk1_2(X1,k3_xboole_0(X2,X1)),X2)), inference(spm,[status(thm)],[c_0_62, c_0_54])).
% 0.78/0.94  cnf(c_0_71, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),k3_tarski(k2_tarski(esk4_0,X2)))|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.78/0.94  cnf(c_0_72, plain, (r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X2)|r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_65, c_0_54])).
% 0.78/0.94  cnf(c_0_73, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.78/0.94  cnf(c_0_74, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.78/0.94  cnf(c_0_75, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[c_0_67, c_0_68])).
% 0.78/0.94  cnf(c_0_76, plain, (r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X1)|r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_69, c_0_54])).
% 0.78/0.94  cnf(c_0_77, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.78/0.94  cnf(c_0_78, negated_conjecture, (r1_tarski(esk3_0,k3_xboole_0(k3_tarski(k2_tarski(esk4_0,X1)),esk3_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.78/0.94  cnf(c_0_79, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_51, c_0_72])).
% 0.78/0.94  cnf(c_0_80, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[c_0_73, c_0_68])).
% 0.78/0.94  cnf(c_0_81, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_47, c_0_32])).
% 0.78/0.94  cnf(c_0_82, plain, (k3_relat_1(X1)=k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_74, c_0_26])).
% 0.78/0.94  cnf(c_0_83, plain, (r1_tarski(X1,k2_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_21, c_0_75])).
% 0.78/0.94  cnf(c_0_84, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))|~r2_hidden(esk1_2(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1)),X3)), inference(spm,[status(thm)],[c_0_62, c_0_76])).
% 0.78/0.94  cnf(c_0_85, negated_conjecture, (k3_xboole_0(k3_tarski(k2_tarski(esk4_0,X1)),esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])])).
% 0.78/0.94  cnf(c_0_86, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_51, c_0_76])).
% 0.78/0.94  cnf(c_0_87, plain, (r1_tarski(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_21, c_0_80])).
% 0.78/0.94  cnf(c_0_88, plain, (r1_tarski(k2_relat_1(X1),k3_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.78/0.94  cnf(c_0_89, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_75]), c_0_68])).
% 0.78/0.94  cnf(c_0_90, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.78/0.94  cnf(c_0_91, plain, (k2_relat_1(X1)=k2_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_77, c_0_75])).
% 0.78/0.94  cnf(c_0_92, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_84, c_0_72])).
% 0.78/0.94  cnf(c_0_93, negated_conjecture, (k3_xboole_0(X1,esk3_0)=esk3_0|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_85, c_0_31])).
% 0.78/0.94  cnf(c_0_94, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_86])).
% 0.78/0.94  cnf(c_0_95, plain, (r1_tarski(k1_relat_1(X1),k3_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_82])).
% 0.78/0.94  cnf(c_0_96, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_80]), c_0_68])).
% 0.78/0.94  cnf(c_0_97, plain, (k1_relat_1(X1)=k1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_77, c_0_80])).
% 0.78/0.94  fof(c_0_98, plain, ![X34, X35, X36]:(~r1_tarski(X34,X35)|~r1_tarski(X36,X35)|r1_tarski(k2_xboole_0(X34,X36),X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.78/0.94  cnf(c_0_99, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_21, c_0_88])).
% 0.78/0.94  cnf(c_0_100, negated_conjecture, (r1_tarski(k2_relat_1(X1),k2_relat_1(esk4_0))|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_22]), c_0_90])])).
% 0.78/0.94  cnf(c_0_101, plain, (k2_relat_1(X1)=k2_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X2,X1)|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_75]), c_0_68])).
% 0.78/0.94  cnf(c_0_102, negated_conjecture, (r1_tarski(esk3_0,k3_xboole_0(esk3_0,X1))|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.78/0.94  cnf(c_0_103, negated_conjecture, (v1_relat_1(k3_xboole_0(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_94]), c_0_90])])).
% 0.78/0.94  cnf(c_0_104, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_21, c_0_95])).
% 0.78/0.94  cnf(c_0_105, negated_conjecture, (r1_tarski(k1_relat_1(X1),k1_relat_1(esk4_0))|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_22]), c_0_90])])).
% 0.78/0.94  cnf(c_0_106, plain, (k1_relat_1(X1)=k1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X2,X1)|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_80]), c_0_68])).
% 0.78/0.94  cnf(c_0_107, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.78/0.94  cnf(c_0_108, negated_conjecture, (r1_tarski(k2_relat_1(X1),k3_relat_1(esk4_0))|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_90])])).
% 0.78/0.94  cnf(c_0_109, negated_conjecture, (k2_relat_1(k3_xboole_0(esk3_0,X1))=k2_relat_1(esk3_0)|~r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_103]), c_0_86])])).
% 0.78/0.94  cnf(c_0_110, negated_conjecture, (r1_tarski(k1_relat_1(X1),k3_relat_1(esk4_0))|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_90])])).
% 0.78/0.94  cnf(c_0_111, negated_conjecture, (k1_relat_1(k3_xboole_0(esk3_0,X1))=k1_relat_1(esk3_0)|~r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_102]), c_0_103]), c_0_86])])).
% 0.78/0.94  cnf(c_0_112, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_107, c_0_26])).
% 0.78/0.94  cnf(c_0_113, negated_conjecture, (r1_tarski(k2_relat_1(esk3_0),k3_relat_1(esk4_0))|~r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_86])])).
% 0.78/0.94  cnf(c_0_114, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),k3_relat_1(esk4_0))|~r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_86])])).
% 0.78/0.94  cnf(c_0_115, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_112, c_0_82])).
% 0.78/0.94  cnf(c_0_116, negated_conjecture, (r1_tarski(k2_relat_1(esk3_0),k3_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_113, c_0_47])).
% 0.78/0.94  cnf(c_0_117, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.78/0.94  cnf(c_0_118, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),k3_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_114, c_0_47])).
% 0.78/0.94  cnf(c_0_119, negated_conjecture, (~r1_tarski(k3_relat_1(esk3_0),k3_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.78/0.94  cnf(c_0_120, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117]), c_0_118])]), c_0_119]), ['proof']).
% 0.78/0.94  # SZS output end CNFRefutation
% 0.78/0.94  # Proof object total steps             : 121
% 0.78/0.94  # Proof object clause steps            : 88
% 0.78/0.94  # Proof object formula steps           : 33
% 0.78/0.94  # Proof object conjectures             : 33
% 0.78/0.94  # Proof object clause conjectures      : 30
% 0.78/0.94  # Proof object formula conjectures     : 3
% 0.78/0.94  # Proof object initial clauses used    : 25
% 0.78/0.94  # Proof object initial formulas used   : 16
% 0.78/0.94  # Proof object generating inferences   : 52
% 0.78/0.94  # Proof object simplifying inferences  : 41
% 0.78/0.94  # Training examples: 0 positive, 0 negative
% 0.78/0.94  # Parsed axioms                        : 16
% 0.78/0.94  # Removed by relevancy pruning/SinE    : 0
% 0.78/0.94  # Initial clauses                      : 30
% 0.78/0.94  # Removed in clause preprocessing      : 1
% 0.78/0.94  # Initial clauses in saturation        : 29
% 0.78/0.94  # Processed clauses                    : 8603
% 0.78/0.94  # ...of these trivial                  : 65
% 0.78/0.94  # ...subsumed                          : 6769
% 0.78/0.94  # ...remaining for further processing  : 1769
% 0.78/0.94  # Other redundant clauses eliminated   : 5
% 0.78/0.94  # Clauses deleted for lack of memory   : 0
% 0.78/0.94  # Backward-subsumed                    : 103
% 0.78/0.94  # Backward-rewritten                   : 38
% 0.78/0.94  # Generated clauses                    : 51686
% 0.78/0.94  # ...of the previous two non-trivial   : 45625
% 0.78/0.94  # Contextual simplify-reflections      : 43
% 0.78/0.94  # Paramodulations                      : 51469
% 0.78/0.94  # Factorizations                       : 212
% 0.78/0.94  # Equation resolutions                 : 5
% 0.78/0.94  # Propositional unsat checks           : 0
% 0.78/0.94  #    Propositional check models        : 0
% 0.78/0.94  #    Propositional check unsatisfiable : 0
% 0.78/0.94  #    Propositional clauses             : 0
% 0.78/0.94  #    Propositional clauses after purity: 0
% 0.78/0.94  #    Propositional unsat core size     : 0
% 0.78/0.94  #    Propositional preprocessing time  : 0.000
% 0.78/0.94  #    Propositional encoding time       : 0.000
% 0.78/0.94  #    Propositional solver time         : 0.000
% 0.78/0.94  #    Success case prop preproc time    : 0.000
% 0.78/0.94  #    Success case prop encoding time   : 0.000
% 0.78/0.94  #    Success case prop solver time     : 0.000
% 0.78/0.94  # Current number of processed clauses  : 1595
% 0.78/0.94  #    Positive orientable unit clauses  : 120
% 0.78/0.94  #    Positive unorientable unit clauses: 2
% 0.78/0.94  #    Negative unit clauses             : 2
% 0.78/0.94  #    Non-unit-clauses                  : 1471
% 0.78/0.94  # Current number of unprocessed clauses: 36388
% 0.78/0.94  # ...number of literals in the above   : 130294
% 0.78/0.94  # Current number of archived formulas  : 0
% 0.78/0.94  # Current number of archived clauses   : 170
% 0.78/0.94  # Clause-clause subsumption calls (NU) : 668489
% 0.78/0.94  # Rec. Clause-clause subsumption calls : 364050
% 0.78/0.94  # Non-unit clause-clause subsumptions  : 5522
% 0.78/0.94  # Unit Clause-clause subsumption calls : 3704
% 0.78/0.94  # Rewrite failures with RHS unbound    : 0
% 0.78/0.94  # BW rewrite match attempts            : 818
% 0.78/0.94  # BW rewrite match successes           : 321
% 0.78/0.94  # Condensation attempts                : 0
% 0.78/0.94  # Condensation successes               : 0
% 0.78/0.94  # Termbank termtop insertions          : 751210
% 0.78/0.94  
% 0.78/0.94  # -------------------------------------------------
% 0.78/0.94  # User time                : 0.580 s
% 0.78/0.94  # System time              : 0.024 s
% 0.78/0.94  # Total time               : 0.603 s
% 0.78/0.94  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
