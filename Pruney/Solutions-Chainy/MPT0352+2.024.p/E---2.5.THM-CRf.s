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
% DateTime   : Thu Dec  3 10:45:39 EST 2020

% Result     : Theorem 37.61s
% Output     : CNFRefutation 37.61s
% Verified   : 
% Statistics : Number of formulae       :  237 (310988 expanded)
%              Number of clauses        :  194 (150061 expanded)
%              Number of leaves         :   21 (77233 expanded)
%              Depth                    :   37
%              Number of atoms          :  457 (760380 expanded)
%              Number of equality atoms :   79 (136395 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t73_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

fof(c_0_22,plain,(
    ! [X52,X53] :
      ( ( ~ m1_subset_1(X53,X52)
        | r2_hidden(X53,X52)
        | v1_xboole_0(X52) )
      & ( ~ r2_hidden(X53,X52)
        | m1_subset_1(X53,X52)
        | v1_xboole_0(X52) )
      & ( ~ m1_subset_1(X53,X52)
        | v1_xboole_0(X53)
        | ~ v1_xboole_0(X52) )
      & ( ~ v1_xboole_0(X53)
        | m1_subset_1(X53,X52)
        | ~ v1_xboole_0(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
    & ( ~ r1_tarski(esk4_0,esk5_0)
      | ~ r1_tarski(k3_subset_1(esk3_0,esk5_0),k3_subset_1(esk3_0,esk4_0)) )
    & ( r1_tarski(esk4_0,esk5_0)
      | r1_tarski(k3_subset_1(esk3_0,esk5_0),k3_subset_1(esk3_0,esk4_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_24,plain,(
    ! [X56] : ~ v1_xboole_0(k1_zfmisc_1(X56)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_25,plain,(
    ! [X43,X44,X45,X46,X47,X48] :
      ( ( ~ r2_hidden(X45,X44)
        | r1_tarski(X45,X43)
        | X44 != k1_zfmisc_1(X43) )
      & ( ~ r1_tarski(X46,X43)
        | r2_hidden(X46,X44)
        | X44 != k1_zfmisc_1(X43) )
      & ( ~ r2_hidden(esk2_2(X47,X48),X48)
        | ~ r1_tarski(esk2_2(X47,X48),X47)
        | X48 = k1_zfmisc_1(X47) )
      & ( r2_hidden(esk2_2(X47,X48),X48)
        | r1_tarski(esk2_2(X47,X48),X47)
        | X48 = k1_zfmisc_1(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_26,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_30]),c_0_29])).

fof(c_0_35,plain,(
    ! [X27,X28,X29] :
      ( ~ r1_tarski(k4_xboole_0(X27,X28),X29)
      | r1_tarski(X27,k2_xboole_0(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_36,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_37,plain,(
    ! [X54,X55] :
      ( ~ m1_subset_1(X55,k1_zfmisc_1(X54))
      | k3_subset_1(X54,X55) = k4_xboole_0(X54,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk5_0,X1)
    | ~ r1_tarski(k1_zfmisc_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_40,plain,(
    ! [X50,X51] :
      ( ~ r1_tarski(X50,X51)
      | r1_tarski(k1_zfmisc_1(X50),k1_zfmisc_1(X51)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

fof(c_0_41,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk4_0,X1)
    | ~ r1_tarski(k1_zfmisc_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_34])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
    ! [X30,X31,X32] :
      ( ~ r1_tarski(X30,k2_xboole_0(X31,X32))
      | ~ r1_xboole_0(X30,X32)
      | r1_tarski(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | ~ r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_50,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | ~ r1_tarski(X21,X22)
      | r1_tarski(X20,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_42])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_44])).

fof(c_0_54,plain,(
    ! [X37,X38,X39] :
      ( ~ r1_tarski(X37,X38)
      | r1_xboole_0(X37,k4_xboole_0(X39,X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

fof(c_0_55,plain,(
    ! [X25,X26] : r1_tarski(k4_xboole_0(X25,X26),X25) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_49])).

fof(c_0_59,plain,(
    ! [X23,X24] :
      ( ~ r1_tarski(X23,X24)
      | k3_xboole_0(X23,X24) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_60,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_61,plain,(
    ! [X33,X34] : r1_xboole_0(k4_xboole_0(X33,X34),X34) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_33])).

fof(c_0_64,plain,(
    ! [X18,X19] : r1_tarski(k3_xboole_0(X18,X19),X18) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_48])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(k3_subset_1(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0)
    | r1_tarski(k3_subset_1(esk3_0,esk5_0),k3_subset_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_68,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_69,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | ~ r1_xboole_0(esk5_0,X2)
    | ~ r1_tarski(esk3_0,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_58])).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_73,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_74,plain,(
    ! [X12,X13] :
      ( ~ r1_xboole_0(X12,X13)
      | r1_xboole_0(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_75,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_77,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_34])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_xboole_0(esk4_0,X2)
    | ~ r1_tarski(esk3_0,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_65])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk5_0,k3_subset_1(esk3_0,esk4_0)))
    | r1_tarski(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_28])])).

cnf(c_0_81,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_68,c_0_44])).

cnf(c_0_82,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_69,c_0_44])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | ~ r1_xboole_0(esk5_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_84,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_85,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_86,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_75,c_0_44])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk5_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_78])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0)
    | ~ r1_xboole_0(esk4_0,k3_subset_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_90,plain,
    ( r1_xboole_0(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_81,c_0_53])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X1)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_82])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | ~ r1_xboole_0(esk5_0,k5_xboole_0(esk3_0,X1))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_93,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_73])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_xboole_0(esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_71])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_77])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_30]),c_0_58])])).

fof(c_0_98,plain,(
    ! [X35,X36] : r1_tarski(X35,k2_xboole_0(X35,X36)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(esk5_0,k2_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_91])).

cnf(c_0_100,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(esk5_0,k3_xboole_0(esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])])).

cnf(c_0_102,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_73])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_xboole_0(esk4_0,k5_xboole_0(esk3_0,X1))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_84])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_73])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(X1,esk5_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_97])).

cnf(c_0_106,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_72])).

cnf(c_0_107,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(X2,esk3_0))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_99])).

cnf(c_0_109,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_73])).

cnf(c_0_110,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102])])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(esk4_0,k3_xboole_0(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_93]),c_0_104])])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(X1,esk5_0)
    | ~ r1_tarski(X2,esk4_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_105])).

cnf(c_0_113,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,esk3_0)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_108])).

cnf(c_0_115,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk5_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_116,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_111]),c_0_102])])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(X1,esk5_0)
    | ~ r1_tarski(X1,k5_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_118,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_119,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk5_0,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_113])])).

cnf(c_0_120,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk4_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_116])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_117,c_0_58])).

cnf(c_0_122,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_123,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_118])).

cnf(c_0_124,negated_conjecture,
    ( X1 = k5_xboole_0(esk5_0,esk5_0)
    | ~ r1_tarski(X1,k5_xboole_0(esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_119])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_120]),c_0_121])])).

cnf(c_0_126,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_29])).

cnf(c_0_127,negated_conjecture,
    ( k5_xboole_0(esk5_0,esk5_0) = k5_xboole_0(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_128,plain,
    ( k5_xboole_0(X1,X2) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_84]),c_0_126])).

cnf(c_0_129,negated_conjecture,
    ( k5_xboole_0(esk4_0,esk4_0) = k3_subset_1(esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_58])])).

cnf(c_0_130,plain,
    ( k5_xboole_0(X1,X1) = X1
    | ~ r1_tarski(X1,k5_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_113])).

cnf(c_0_131,negated_conjecture,
    ( k3_subset_1(esk5_0,esk5_0) = k3_subset_1(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_58])])).

cnf(c_0_132,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | ~ r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_100,c_0_48])).

cnf(c_0_133,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_72])).

cnf(c_0_134,plain,
    ( k3_subset_1(X1,X1) = X1
    | ~ r1_tarski(X1,k3_subset_1(X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_128]),c_0_58])])).

cnf(c_0_135,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk4_0,esk4_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_129]),c_0_131])).

cnf(c_0_136,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_132,c_0_48])).

cnf(c_0_137,plain,
    ( r1_xboole_0(k3_subset_1(X1,X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_128]),c_0_58])])).

cnf(c_0_138,negated_conjecture,
    ( k3_subset_1(k3_subset_1(esk4_0,esk4_0),k3_subset_1(esk4_0,esk4_0)) = k3_subset_1(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_134,c_0_135])).

cnf(c_0_139,plain,
    ( k1_zfmisc_1(k3_xboole_0(X1,X2)) = k1_zfmisc_1(X1)
    | ~ r1_tarski(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_136,c_0_77])).

cnf(c_0_140,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_77])).

cnf(c_0_141,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_82])).

cnf(c_0_142,plain,
    ( k1_zfmisc_1(k2_xboole_0(X1,X2)) = k1_zfmisc_1(X1)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_136,c_0_107])).

cnf(c_0_143,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk4_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_135])])).

cnf(c_0_144,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(k3_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_139])).

cnf(c_0_145,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk4_0,esk4_0),X1) = k5_xboole_0(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_140,c_0_125])).

cnf(c_0_146,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_141])).

cnf(c_0_147,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k2_xboole_0(X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_126,c_0_142])).

cnf(c_0_148,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X1)
    | ~ r1_xboole_0(k2_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_58])).

cnf(c_0_149,negated_conjecture,
    ( r1_xboole_0(X1,k3_subset_1(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_143])).

cnf(c_0_150,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(X3),X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_123])).

cnf(c_0_151,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(k5_xboole_0(esk4_0,esk4_0)),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_145]),c_0_125]),c_0_125])])).

cnf(c_0_152,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_146,c_0_81])).

cnf(c_0_153,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_73])).

cnf(c_0_154,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_128]),c_0_58])])).

cnf(c_0_155,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1))
    | ~ r1_tarski(k2_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_147,c_0_107])).

cnf(c_0_156,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,k3_subset_1(esk4_0,esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_148,c_0_149])).

fof(c_0_157,plain,(
    ! [X40,X41,X42] :
      ( ~ r1_tarski(X40,X41)
      | ~ r1_xboole_0(X40,X42)
      | r1_tarski(X40,k4_xboole_0(X41,X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

cnf(c_0_158,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k5_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_150,c_0_151])).

cnf(c_0_159,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_154])])).

cnf(c_0_160,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_155,c_0_156])).

cnf(c_0_161,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,X2))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_81,c_0_72])).

cnf(c_0_162,negated_conjecture,
    ( r1_tarski(X1,esk5_0)
    | ~ r1_tarski(X1,k3_xboole_0(esk4_0,X2)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_77])).

cnf(c_0_163,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_157])).

cnf(c_0_164,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_102])).

cnf(c_0_165,negated_conjecture,
    ( r2_hidden(k5_xboole_0(esk4_0,esk4_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_158,c_0_125])).

cnf(c_0_166,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_159,c_0_160])])).

cnf(c_0_167,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X2,X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_161,c_0_113])).

cnf(c_0_168,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_162,c_0_58])).

cnf(c_0_169,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[c_0_163,c_0_44])).

cnf(c_0_170,negated_conjecture,
    ( k3_xboole_0(X1,k5_xboole_0(esk4_0,esk4_0)) = k5_xboole_0(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_164,c_0_125])).

cnf(c_0_171,negated_conjecture,
    ( m1_subset_1(k5_xboole_0(esk4_0,esk4_0),k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_165]),c_0_29])).

cnf(c_0_172,negated_conjecture,
    ( X1 = k5_xboole_0(esk4_0,esk4_0)
    | ~ r1_tarski(X1,k5_xboole_0(esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_127]),c_0_127])).

cnf(c_0_173,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_82])).

cnf(c_0_174,plain,
    ( X1 = k3_subset_1(X2,X2)
    | ~ r1_tarski(X1,k3_subset_1(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_166])).

cnf(c_0_175,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_167]),c_0_58])])).

cnf(c_0_176,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk5_0))
    | ~ r1_tarski(esk4_0,k3_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_144,c_0_168])).

cnf(c_0_177,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_100,c_0_82])).

cnf(c_0_178,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_169,c_0_81])).

cnf(c_0_179,negated_conjecture,
    ( k3_xboole_0(X1,k3_subset_1(esk4_0,esk4_0)) = k3_subset_1(esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_170,c_0_129]),c_0_129]),c_0_131]),c_0_131])).

cnf(c_0_180,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk4_0,esk4_0),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_171,c_0_129]),c_0_131])).

cnf(c_0_181,negated_conjecture,
    ( X1 = k3_subset_1(esk4_0,esk4_0)
    | ~ r1_tarski(X1,k3_subset_1(esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_172,c_0_129]),c_0_129]),c_0_131]),c_0_131])).

cnf(c_0_182,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_173,c_0_53])).

cnf(c_0_183,plain,
    ( k5_xboole_0(X1,X1) = k3_subset_1(X2,X2) ),
    inference(spm,[status(thm)],[c_0_174,c_0_175])).

cnf(c_0_184,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1)))))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_169,c_0_93])).

cnf(c_0_185,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk5_0))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_72]),c_0_58])])).

cnf(c_0_186,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = X1
    | ~ r1_tarski(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_178]),c_0_58])])).

cnf(c_0_187,negated_conjecture,
    ( k3_xboole_0(k3_subset_1(esk4_0,esk4_0),X1) = k3_subset_1(esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_145,c_0_129]),c_0_129]),c_0_131]),c_0_131])).

cnf(c_0_188,negated_conjecture,
    ( k5_xboole_0(X1,k3_subset_1(esk4_0,esk4_0)) = k3_subset_1(X1,k3_subset_1(esk4_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_179]),c_0_180])])).

cnf(c_0_189,negated_conjecture,
    ( k3_subset_1(X1,X1) = k3_subset_1(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_181,c_0_166])).

cnf(c_0_190,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_183]),c_0_160])])).

cnf(c_0_191,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1))))
    | ~ r1_tarski(k5_xboole_0(X3,k3_xboole_0(X3,X1)),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_184,c_0_84])).

cnf(c_0_192,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_105]),c_0_58])])).

cnf(c_0_193,negated_conjecture,
    ( k3_subset_1(X1,k3_subset_1(esk4_0,esk4_0)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_187]),c_0_188]),c_0_189]),c_0_179]),c_0_188])).

cnf(c_0_194,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_107])).

cnf(c_0_195,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190,c_0_191]),c_0_58])])).

cnf(c_0_196,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_184]),c_0_58])])).

cnf(c_0_197,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk5_0) = k3_subset_1(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_110]),c_0_28])])).

cnf(c_0_198,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk5_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_150,c_0_192])).

cnf(c_0_199,negated_conjecture,
    ( k3_subset_1(X1,k3_subset_1(esk4_0,esk4_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_193,c_0_194])).

cnf(c_0_200,negated_conjecture,
    ( k3_subset_1(X1,X1) = k3_subset_1(X2,X2) ),
    inference(spm,[status(thm)],[c_0_189,c_0_189])).

cnf(c_0_201,plain,
    ( k3_subset_1(X1,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,k3_subset_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_177,c_0_53])).

cnf(c_0_202,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,X1))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_195,c_0_84])).

cnf(c_0_203,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_subset_1(esk3_0,esk5_0))) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196,c_0_110]),c_0_197])).

cnf(c_0_204,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(esk5_0),X2)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_198])).

cnf(c_0_205,plain,
    ( k5_xboole_0(X1,X1) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_72])).

cnf(c_0_206,negated_conjecture,
    ( k3_subset_1(X1,k3_subset_1(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_199,c_0_200])).

cnf(c_0_207,negated_conjecture,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_180,c_0_189])).

cnf(c_0_208,plain,
    ( k5_xboole_0(X1,X1) = X2
    | ~ r1_tarski(X2,k5_xboole_0(X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201,c_0_183]),c_0_160])])).

cnf(c_0_209,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk5_0,k3_subset_1(esk3_0,esk5_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_202,c_0_203]),c_0_77])])).

cnf(c_0_210,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk4_0) = k3_subset_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_116]),c_0_30])])).

cnf(c_0_211,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(esk5_0),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_204])).

cnf(c_0_212,negated_conjecture,
    ( k5_xboole_0(X1,X1) = X1
    | ~ r1_tarski(X1,k3_subset_1(X2,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205,c_0_206]),c_0_207])])).

cnf(c_0_213,negated_conjecture,
    ( k5_xboole_0(X1,X1) = k3_xboole_0(esk5_0,k3_subset_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_208,c_0_209])).

cnf(c_0_214,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_subset_1(esk3_0,esk4_0))) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196,c_0_116]),c_0_210])).

cnf(c_0_215,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_tarski(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_211,c_0_48])).

cnf(c_0_216,negated_conjecture,
    ( k5_xboole_0(X1,k3_subset_1(esk4_0,esk4_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_188,c_0_199])).

cnf(c_0_217,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_subset_1(esk3_0,esk5_0)) = X1
    | ~ r1_tarski(X1,k3_subset_1(X2,X2)) ),
    inference(rw,[status(thm)],[c_0_212,c_0_213])).

cnf(c_0_218,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,k3_subset_1(esk3_0,esk4_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_202,c_0_214]),c_0_77])])).

cnf(c_0_219,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,X1),X2)
    | ~ r1_tarski(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_215,c_0_77])).

cnf(c_0_220,negated_conjecture,
    ( r1_xboole_0(X1,esk5_0)
    | ~ r1_tarski(X1,k3_subset_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_203])).

cnf(c_0_221,negated_conjecture,
    ( k5_xboole_0(X1,k3_subset_1(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_216,c_0_200])).

cnf(c_0_222,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_subset_1(esk3_0,esk5_0)) = k3_xboole_0(esk4_0,k3_subset_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_217,c_0_218])).

cnf(c_0_223,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,X1),X2)
    | ~ r1_xboole_0(k3_xboole_0(esk4_0,X1),X3)
    | ~ r1_tarski(esk5_0,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_219])).

cnf(c_0_224,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(X1,k3_subset_1(esk3_0,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_220,c_0_102])).

cnf(c_0_225,negated_conjecture,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_221,c_0_183])).

cnf(c_0_226,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X3) ),
    inference(spm,[status(thm)],[c_0_169,c_0_109])).

cnf(c_0_227,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_subset_1(esk3_0,esk4_0)) = X1
    | ~ r1_tarski(X1,k3_subset_1(X2,X2)) ),
    inference(rw,[status(thm)],[c_0_217,c_0_222])).

cnf(c_0_228,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,k3_subset_1(esk3_0,esk5_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_223,c_0_224]),c_0_141])])).

cnf(c_0_229,negated_conjecture,
    ( k5_xboole_0(X1,k3_xboole_0(esk5_0,k3_subset_1(esk3_0,esk5_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_225,c_0_213])).

cnf(c_0_230,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk5_0)
    | ~ r1_tarski(k3_subset_1(esk3_0,esk5_0),k3_subset_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_231,negated_conjecture,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(esk4_0,X1)),k3_subset_1(esk3_0,esk4_0))
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(esk4_0,X1)),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_226,c_0_116]),c_0_210])).

cnf(c_0_232,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_subset_1(esk3_0,esk5_0)) = k3_xboole_0(esk4_0,k3_subset_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_227,c_0_228])).

cnf(c_0_233,negated_conjecture,
    ( k5_xboole_0(X1,k3_xboole_0(esk4_0,k3_subset_1(esk3_0,esk4_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_229,c_0_222])).

cnf(c_0_234,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk3_0,esk5_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_110]),c_0_197])).

cnf(c_0_235,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk3_0,esk5_0),k3_subset_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_230,c_0_97])])).

cnf(c_0_236,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_231,c_0_232]),c_0_233]),c_0_233]),c_0_234])]),c_0_235]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 37.61/37.80  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 37.61/37.80  # and selection function SelectComplexExceptUniqMaxHorn.
% 37.61/37.80  #
% 37.61/37.80  # Preprocessing time       : 0.028 s
% 37.61/37.80  # Presaturation interreduction done
% 37.61/37.80  
% 37.61/37.80  # Proof found!
% 37.61/37.80  # SZS status Theorem
% 37.61/37.80  # SZS output start CNFRefutation
% 37.61/37.80  fof(t31_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 37.61/37.80  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 37.61/37.80  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 37.61/37.80  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 37.61/37.80  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 37.61/37.80  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 37.61/37.80  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 37.61/37.80  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 37.61/37.80  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 37.61/37.80  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 37.61/37.80  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 37.61/37.80  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 37.61/37.80  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 37.61/37.80  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 37.61/37.80  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 37.61/37.80  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 37.61/37.80  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 37.61/37.80  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 37.61/37.80  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 37.61/37.80  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 37.61/37.80  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 37.61/37.80  fof(c_0_21, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_subset_1])).
% 37.61/37.80  fof(c_0_22, plain, ![X52, X53]:(((~m1_subset_1(X53,X52)|r2_hidden(X53,X52)|v1_xboole_0(X52))&(~r2_hidden(X53,X52)|m1_subset_1(X53,X52)|v1_xboole_0(X52)))&((~m1_subset_1(X53,X52)|v1_xboole_0(X53)|~v1_xboole_0(X52))&(~v1_xboole_0(X53)|m1_subset_1(X53,X52)|~v1_xboole_0(X52)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 37.61/37.80  fof(c_0_23, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))&((~r1_tarski(esk4_0,esk5_0)|~r1_tarski(k3_subset_1(esk3_0,esk5_0),k3_subset_1(esk3_0,esk4_0)))&(r1_tarski(esk4_0,esk5_0)|r1_tarski(k3_subset_1(esk3_0,esk5_0),k3_subset_1(esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 37.61/37.80  fof(c_0_24, plain, ![X56]:~v1_xboole_0(k1_zfmisc_1(X56)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 37.61/37.80  fof(c_0_25, plain, ![X43, X44, X45, X46, X47, X48]:(((~r2_hidden(X45,X44)|r1_tarski(X45,X43)|X44!=k1_zfmisc_1(X43))&(~r1_tarski(X46,X43)|r2_hidden(X46,X44)|X44!=k1_zfmisc_1(X43)))&((~r2_hidden(esk2_2(X47,X48),X48)|~r1_tarski(esk2_2(X47,X48),X47)|X48=k1_zfmisc_1(X47))&(r2_hidden(esk2_2(X47,X48),X48)|r1_tarski(esk2_2(X47,X48),X47)|X48=k1_zfmisc_1(X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 37.61/37.80  fof(c_0_26, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 37.61/37.80  cnf(c_0_27, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 37.61/37.80  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 37.61/37.80  cnf(c_0_29, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 37.61/37.80  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 37.61/37.80  cnf(c_0_31, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 37.61/37.80  cnf(c_0_32, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 37.61/37.80  cnf(c_0_33, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 37.61/37.80  cnf(c_0_34, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_30]), c_0_29])).
% 37.61/37.80  fof(c_0_35, plain, ![X27, X28, X29]:(~r1_tarski(k4_xboole_0(X27,X28),X29)|r1_tarski(X27,k2_xboole_0(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 37.61/37.80  fof(c_0_36, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 37.61/37.80  fof(c_0_37, plain, ![X54, X55]:(~m1_subset_1(X55,k1_zfmisc_1(X54))|k3_subset_1(X54,X55)=k4_xboole_0(X54,X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 37.61/37.80  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_31])).
% 37.61/37.80  cnf(c_0_39, negated_conjecture, (r2_hidden(esk5_0,X1)|~r1_tarski(k1_zfmisc_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 37.61/37.80  fof(c_0_40, plain, ![X50, X51]:(~r1_tarski(X50,X51)|r1_tarski(k1_zfmisc_1(X50),k1_zfmisc_1(X51))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 37.61/37.80  fof(c_0_41, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 37.61/37.80  cnf(c_0_42, negated_conjecture, (r2_hidden(esk4_0,X1)|~r1_tarski(k1_zfmisc_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_34])).
% 37.61/37.80  cnf(c_0_43, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 37.61/37.80  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 37.61/37.80  cnf(c_0_45, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 37.61/37.80  fof(c_0_46, plain, ![X30, X31, X32]:(~r1_tarski(X30,k2_xboole_0(X31,X32))|~r1_xboole_0(X30,X32)|r1_tarski(X30,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 37.61/37.80  cnf(c_0_47, negated_conjecture, (r1_tarski(esk5_0,X1)|~r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 37.61/37.80  cnf(c_0_48, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 37.61/37.80  cnf(c_0_49, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 37.61/37.80  fof(c_0_50, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|~r1_tarski(X21,X22)|r1_tarski(X20,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 37.61/37.80  cnf(c_0_51, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_42])).
% 37.61/37.80  cnf(c_0_52, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 37.61/37.80  cnf(c_0_53, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_45, c_0_44])).
% 37.61/37.80  fof(c_0_54, plain, ![X37, X38, X39]:(~r1_tarski(X37,X38)|r1_xboole_0(X37,k4_xboole_0(X39,X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 37.61/37.80  fof(c_0_55, plain, ![X25, X26]:r1_tarski(k4_xboole_0(X25,X26),X25), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 37.61/37.80  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 37.61/37.80  cnf(c_0_57, negated_conjecture, (r1_tarski(esk5_0,X1)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 37.61/37.80  cnf(c_0_58, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_49])).
% 37.61/37.80  fof(c_0_59, plain, ![X23, X24]:(~r1_tarski(X23,X24)|k3_xboole_0(X23,X24)=X23), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 37.61/37.80  fof(c_0_60, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 37.61/37.80  fof(c_0_61, plain, ![X33, X34]:r1_xboole_0(k4_xboole_0(X33,X34),X34), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 37.61/37.80  cnf(c_0_62, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 37.61/37.80  cnf(c_0_63, negated_conjecture, (r1_tarski(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_33])).
% 37.61/37.80  fof(c_0_64, plain, ![X18, X19]:r1_tarski(k3_xboole_0(X18,X19),X18), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 37.61/37.80  cnf(c_0_65, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_51, c_0_48])).
% 37.61/37.80  cnf(c_0_66, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(k3_subset_1(X1,X2),X3)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 37.61/37.80  cnf(c_0_67, negated_conjecture, (r1_tarski(esk4_0,esk5_0)|r1_tarski(k3_subset_1(esk3_0,esk5_0),k3_subset_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 37.61/37.80  cnf(c_0_68, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 37.61/37.80  cnf(c_0_69, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 37.61/37.80  cnf(c_0_70, negated_conjecture, (r1_tarski(esk5_0,X1)|~r1_xboole_0(esk5_0,X2)|~r1_tarski(esk3_0,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 37.61/37.80  cnf(c_0_71, plain, (r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_52, c_0_58])).
% 37.61/37.80  cnf(c_0_72, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 37.61/37.80  cnf(c_0_73, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 37.61/37.80  fof(c_0_74, plain, ![X12, X13]:(~r1_xboole_0(X12,X13)|r1_xboole_0(X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 37.61/37.80  cnf(c_0_75, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 37.61/37.80  cnf(c_0_76, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 37.61/37.80  cnf(c_0_77, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 37.61/37.80  cnf(c_0_78, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_34])).
% 37.61/37.80  cnf(c_0_79, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_xboole_0(esk4_0,X2)|~r1_tarski(esk3_0,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_56, c_0_65])).
% 37.61/37.80  cnf(c_0_80, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk5_0,k3_subset_1(esk3_0,esk4_0)))|r1_tarski(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_28])])).
% 37.61/37.80  cnf(c_0_81, plain, (r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_68, c_0_44])).
% 37.61/37.80  cnf(c_0_82, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_69, c_0_44])).
% 37.61/37.80  cnf(c_0_83, negated_conjecture, (r1_tarski(esk5_0,X1)|~r1_xboole_0(esk5_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 37.61/37.80  cnf(c_0_84, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 37.61/37.80  cnf(c_0_85, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 37.61/37.80  cnf(c_0_86, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_75, c_0_44])).
% 37.61/37.80  cnf(c_0_87, negated_conjecture, (r1_tarski(k3_xboole_0(esk5_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 37.61/37.80  cnf(c_0_88, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_62, c_0_78])).
% 37.61/37.80  cnf(c_0_89, negated_conjecture, (r1_tarski(esk4_0,esk5_0)|~r1_xboole_0(esk4_0,k3_subset_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 37.61/37.80  cnf(c_0_90, plain, (r1_xboole_0(X1,k3_subset_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_81, c_0_53])).
% 37.61/37.80  cnf(c_0_91, negated_conjecture, (r1_tarski(k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X1)),esk3_0)), inference(spm,[status(thm)],[c_0_76, c_0_82])).
% 37.61/37.80  cnf(c_0_92, negated_conjecture, (r1_tarski(esk5_0,X1)|~r1_xboole_0(esk5_0,k5_xboole_0(esk3_0,X1))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 37.61/37.80  cnf(c_0_93, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 37.61/37.80  cnf(c_0_94, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_87, c_0_73])).
% 37.61/37.80  cnf(c_0_95, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_xboole_0(esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_79, c_0_71])).
% 37.61/37.80  cnf(c_0_96, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_88, c_0_77])).
% 37.61/37.80  cnf(c_0_97, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_30]), c_0_58])])).
% 37.61/37.80  fof(c_0_98, plain, ![X35, X36]:r1_tarski(X35,k2_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 37.61/37.80  cnf(c_0_99, negated_conjecture, (r1_tarski(esk5_0,k2_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_52, c_0_91])).
% 37.61/37.80  cnf(c_0_100, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 37.61/37.80  cnf(c_0_101, negated_conjecture, (r1_tarski(esk5_0,k3_xboole_0(esk3_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])])).
% 37.61/37.80  cnf(c_0_102, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_77, c_0_73])).
% 37.61/37.80  cnf(c_0_103, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_xboole_0(esk4_0,k5_xboole_0(esk3_0,X1))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_95, c_0_84])).
% 37.61/37.80  cnf(c_0_104, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_96, c_0_73])).
% 37.61/37.80  cnf(c_0_105, negated_conjecture, (r1_tarski(X1,esk5_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_62, c_0_97])).
% 37.61/37.80  cnf(c_0_106, plain, (r1_tarski(k5_xboole_0(X1,X1),X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_82, c_0_72])).
% 37.61/37.80  cnf(c_0_107, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 37.61/37.80  cnf(c_0_108, negated_conjecture, (r1_tarski(X1,k2_xboole_0(X2,esk3_0))|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_62, c_0_99])).
% 37.61/37.80  cnf(c_0_109, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X2)), inference(spm,[status(thm)],[c_0_86, c_0_73])).
% 37.61/37.80  cnf(c_0_110, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102])])).
% 37.61/37.80  cnf(c_0_111, negated_conjecture, (r1_tarski(esk4_0,k3_xboole_0(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_93]), c_0_104])])).
% 37.61/37.80  cnf(c_0_112, negated_conjecture, (r1_tarski(X1,esk5_0)|~r1_tarski(X2,esk4_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_62, c_0_105])).
% 37.61/37.80  cnf(c_0_113, plain, (r1_tarski(k5_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 37.61/37.80  cnf(c_0_114, negated_conjecture, (r1_tarski(X1,X2)|~r1_xboole_0(X1,esk3_0)|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_56, c_0_108])).
% 37.61/37.80  cnf(c_0_115, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk5_0,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 37.61/37.80  cnf(c_0_116, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_111]), c_0_102])])).
% 37.61/37.80  cnf(c_0_117, negated_conjecture, (r1_tarski(X1,esk5_0)|~r1_tarski(X1,k5_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 37.61/37.80  cnf(c_0_118, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 37.61/37.80  cnf(c_0_119, negated_conjecture, (r1_tarski(k5_xboole_0(esk5_0,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_113])])).
% 37.61/37.80  cnf(c_0_120, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk4_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_109, c_0_116])).
% 37.61/37.80  cnf(c_0_121, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_117, c_0_58])).
% 37.61/37.80  cnf(c_0_122, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 37.61/37.80  cnf(c_0_123, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_118])).
% 37.61/37.80  cnf(c_0_124, negated_conjecture, (X1=k5_xboole_0(esk5_0,esk5_0)|~r1_tarski(X1,k5_xboole_0(esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_100, c_0_119])).
% 37.61/37.80  cnf(c_0_125, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_120]), c_0_121])])).
% 37.61/37.80  cnf(c_0_126, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_29])).
% 37.61/37.80  cnf(c_0_127, negated_conjecture, (k5_xboole_0(esk5_0,esk5_0)=k5_xboole_0(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_124, c_0_125])).
% 37.61/37.80  cnf(c_0_128, plain, (k5_xboole_0(X1,X2)=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_84]), c_0_126])).
% 37.61/37.80  cnf(c_0_129, negated_conjecture, (k5_xboole_0(esk4_0,esk4_0)=k3_subset_1(esk5_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_58])])).
% 37.61/37.80  cnf(c_0_130, plain, (k5_xboole_0(X1,X1)=X1|~r1_tarski(X1,k5_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_100, c_0_113])).
% 37.61/37.80  cnf(c_0_131, negated_conjecture, (k3_subset_1(esk5_0,esk5_0)=k3_subset_1(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_58])])).
% 37.61/37.80  cnf(c_0_132, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|~r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_100, c_0_48])).
% 37.61/37.80  cnf(c_0_133, plain, (r1_xboole_0(k5_xboole_0(X1,X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_86, c_0_72])).
% 37.61/37.80  cnf(c_0_134, plain, (k3_subset_1(X1,X1)=X1|~r1_tarski(X1,k3_subset_1(X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_128]), c_0_58])])).
% 37.61/37.80  cnf(c_0_135, negated_conjecture, (r1_tarski(k3_subset_1(esk4_0,esk4_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125, c_0_129]), c_0_131])).
% 37.61/37.80  cnf(c_0_136, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|~r1_tarski(X2,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_132, c_0_48])).
% 37.61/37.80  cnf(c_0_137, plain, (r1_xboole_0(k3_subset_1(X1,X1),X2)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_128]), c_0_58])])).
% 37.61/37.80  cnf(c_0_138, negated_conjecture, (k3_subset_1(k3_subset_1(esk4_0,esk4_0),k3_subset_1(esk4_0,esk4_0))=k3_subset_1(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_134, c_0_135])).
% 37.61/37.80  cnf(c_0_139, plain, (k1_zfmisc_1(k3_xboole_0(X1,X2))=k1_zfmisc_1(X1)|~r1_tarski(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_136, c_0_77])).
% 37.61/37.80  cnf(c_0_140, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_100, c_0_77])).
% 37.61/37.80  cnf(c_0_141, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_52, c_0_82])).
% 37.61/37.80  cnf(c_0_142, plain, (k1_zfmisc_1(k2_xboole_0(X1,X2))=k1_zfmisc_1(X1)|~r1_tarski(k2_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_136, c_0_107])).
% 37.61/37.80  cnf(c_0_143, negated_conjecture, (r1_xboole_0(k3_subset_1(esk4_0,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_135])])).
% 37.61/37.80  cnf(c_0_144, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(k3_xboole_0(X1,X3),X2)|~r1_tarski(X1,k3_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_48, c_0_139])).
% 37.61/37.80  cnf(c_0_145, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk4_0,esk4_0),X1)=k5_xboole_0(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_140, c_0_125])).
% 37.61/37.80  cnf(c_0_146, plain, (r1_tarski(X1,X2)|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_56, c_0_141])).
% 37.61/37.80  cnf(c_0_147, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k2_xboole_0(X2,X3),X2)), inference(spm,[status(thm)],[c_0_126, c_0_142])).
% 37.61/37.80  cnf(c_0_148, plain, (r1_tarski(k2_xboole_0(X1,X2),X1)|~r1_xboole_0(k2_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_56, c_0_58])).
% 37.61/37.80  cnf(c_0_149, negated_conjecture, (r1_xboole_0(X1,k3_subset_1(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_85, c_0_143])).
% 37.61/37.80  cnf(c_0_150, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_zfmisc_1(X3),X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_32, c_0_123])).
% 37.61/37.80  cnf(c_0_151, negated_conjecture, (r1_tarski(k1_zfmisc_1(k5_xboole_0(esk4_0,esk4_0)),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_145]), c_0_125]), c_0_125])])).
% 37.61/37.80  cnf(c_0_152, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_146, c_0_81])).
% 37.61/37.80  cnf(c_0_153, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_53, c_0_73])).
% 37.61/37.80  cnf(c_0_154, plain, (r1_tarski(k3_subset_1(X1,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_128]), c_0_58])])).
% 37.61/37.80  cnf(c_0_155, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))|~r1_tarski(k2_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_147, c_0_107])).
% 37.61/37.80  cnf(c_0_156, negated_conjecture, (r1_tarski(k2_xboole_0(X1,k3_subset_1(esk4_0,esk4_0)),X1)), inference(spm,[status(thm)],[c_0_148, c_0_149])).
% 37.61/37.80  fof(c_0_157, plain, ![X40, X41, X42]:(~r1_tarski(X40,X41)|~r1_xboole_0(X40,X42)|r1_tarski(X40,k4_xboole_0(X41,X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 37.61/37.80  cnf(c_0_158, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k5_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_150, c_0_151])).
% 37.61/37.80  cnf(c_0_159, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~m1_subset_1(X1,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_153]), c_0_154])])).
% 37.61/37.80  cnf(c_0_160, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_155, c_0_156])).
% 37.61/37.80  cnf(c_0_161, plain, (r1_xboole_0(X1,k5_xboole_0(X2,X2))|~r1_tarski(X1,X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_81, c_0_72])).
% 37.61/37.80  cnf(c_0_162, negated_conjecture, (r1_tarski(X1,esk5_0)|~r1_tarski(X1,k3_xboole_0(esk4_0,X2))), inference(spm,[status(thm)],[c_0_112, c_0_77])).
% 37.61/37.80  cnf(c_0_163, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_157])).
% 37.61/37.80  cnf(c_0_164, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_100, c_0_102])).
% 37.61/37.80  cnf(c_0_165, negated_conjecture, (r2_hidden(k5_xboole_0(esk4_0,esk4_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_158, c_0_125])).
% 37.61/37.80  cnf(c_0_166, plain, (r1_tarski(k3_subset_1(X1,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_159, c_0_160])])).
% 37.61/37.80  cnf(c_0_167, plain, (r1_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X2,X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_161, c_0_113])).
% 37.61/37.80  cnf(c_0_168, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_162, c_0_58])).
% 37.61/37.80  cnf(c_0_169, plain, (r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(rw,[status(thm)],[c_0_163, c_0_44])).
% 37.61/37.80  cnf(c_0_170, negated_conjecture, (k3_xboole_0(X1,k5_xboole_0(esk4_0,esk4_0))=k5_xboole_0(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_164, c_0_125])).
% 37.61/37.80  cnf(c_0_171, negated_conjecture, (m1_subset_1(k5_xboole_0(esk4_0,esk4_0),k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_165]), c_0_29])).
% 37.61/37.80  cnf(c_0_172, negated_conjecture, (X1=k5_xboole_0(esk4_0,esk4_0)|~r1_tarski(X1,k5_xboole_0(esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_127]), c_0_127])).
% 37.61/37.80  cnf(c_0_173, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_62, c_0_82])).
% 37.61/37.80  cnf(c_0_174, plain, (X1=k3_subset_1(X2,X2)|~r1_tarski(X1,k3_subset_1(X2,X2))), inference(spm,[status(thm)],[c_0_100, c_0_166])).
% 37.61/37.80  cnf(c_0_175, plain, (r1_tarski(k5_xboole_0(X1,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_167]), c_0_58])])).
% 37.61/37.80  cnf(c_0_176, negated_conjecture, (r1_tarski(k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk5_0))|~r1_tarski(esk4_0,k3_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_144, c_0_168])).
% 37.61/37.80  cnf(c_0_177, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_100, c_0_82])).
% 37.61/37.80  cnf(c_0_178, plain, (r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))))|~r1_tarski(X1,X2)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_169, c_0_81])).
% 37.61/37.80  cnf(c_0_179, negated_conjecture, (k3_xboole_0(X1,k3_subset_1(esk4_0,esk4_0))=k3_subset_1(esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_170, c_0_129]), c_0_129]), c_0_131]), c_0_131])).
% 37.61/37.80  cnf(c_0_180, negated_conjecture, (m1_subset_1(k3_subset_1(esk4_0,esk4_0),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_171, c_0_129]), c_0_131])).
% 37.61/37.80  cnf(c_0_181, negated_conjecture, (X1=k3_subset_1(esk4_0,esk4_0)|~r1_tarski(X1,k3_subset_1(esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_172, c_0_129]), c_0_129]), c_0_131]), c_0_131])).
% 37.61/37.80  cnf(c_0_182, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X3))), inference(spm,[status(thm)],[c_0_173, c_0_53])).
% 37.61/37.80  cnf(c_0_183, plain, (k5_xboole_0(X1,X1)=k3_subset_1(X2,X2)), inference(spm,[status(thm)],[c_0_174, c_0_175])).
% 37.61/37.80  cnf(c_0_184, plain, (r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1)))))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_169, c_0_93])).
% 37.61/37.80  cnf(c_0_185, negated_conjecture, (r1_tarski(k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk5_0))|~r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176, c_0_72]), c_0_58])])).
% 37.61/37.80  cnf(c_0_186, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))=X1|~r1_tarski(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177, c_0_178]), c_0_58])])).
% 37.61/37.80  cnf(c_0_187, negated_conjecture, (k3_xboole_0(k3_subset_1(esk4_0,esk4_0),X1)=k3_subset_1(esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_145, c_0_129]), c_0_129]), c_0_131]), c_0_131])).
% 37.61/37.80  cnf(c_0_188, negated_conjecture, (k5_xboole_0(X1,k3_subset_1(esk4_0,esk4_0))=k3_subset_1(X1,k3_subset_1(esk4_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_179]), c_0_180])])).
% 37.61/37.80  cnf(c_0_189, negated_conjecture, (k3_subset_1(X1,X1)=k3_subset_1(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_181, c_0_166])).
% 37.61/37.80  cnf(c_0_190, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182, c_0_183]), c_0_160])])).
% 37.61/37.80  cnf(c_0_191, plain, (r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1))))|~r1_tarski(k5_xboole_0(X3,k3_xboole_0(X3,X1)),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_184, c_0_84])).
% 37.61/37.80  cnf(c_0_192, negated_conjecture, (r1_tarski(k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185, c_0_105]), c_0_58])])).
% 37.61/37.80  cnf(c_0_193, negated_conjecture, (k3_subset_1(X1,k3_subset_1(esk4_0,esk4_0))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186, c_0_187]), c_0_188]), c_0_189]), c_0_179]), c_0_188])).
% 37.61/37.80  cnf(c_0_194, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)))), inference(spm,[status(thm)],[c_0_52, c_0_107])).
% 37.61/37.80  cnf(c_0_195, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190, c_0_191]), c_0_58])])).
% 37.61/37.80  cnf(c_0_196, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177, c_0_184]), c_0_58])])).
% 37.61/37.80  cnf(c_0_197, negated_conjecture, (k5_xboole_0(esk3_0,esk5_0)=k3_subset_1(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_110]), c_0_28])])).
% 37.61/37.80  cnf(c_0_198, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(esk5_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_150, c_0_192])).
% 37.61/37.80  cnf(c_0_199, negated_conjecture, (k3_subset_1(X1,k3_subset_1(esk4_0,esk4_0))=X1), inference(spm,[status(thm)],[c_0_193, c_0_194])).
% 37.61/37.80  cnf(c_0_200, negated_conjecture, (k3_subset_1(X1,X1)=k3_subset_1(X2,X2)), inference(spm,[status(thm)],[c_0_189, c_0_189])).
% 37.61/37.80  cnf(c_0_201, plain, (k3_subset_1(X1,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,k3_subset_1(X1,X2))), inference(spm,[status(thm)],[c_0_177, c_0_53])).
% 37.61/37.80  cnf(c_0_202, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,X1))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_195, c_0_84])).
% 37.61/37.80  cnf(c_0_203, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_subset_1(esk3_0,esk5_0)))=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196, c_0_110]), c_0_197])).
% 37.61/37.80  cnf(c_0_204, negated_conjecture, (r2_hidden(X1,X2)|~r1_tarski(k1_zfmisc_1(esk5_0),X2)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_198])).
% 37.61/37.80  cnf(c_0_205, plain, (k5_xboole_0(X1,X1)=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_53, c_0_72])).
% 37.61/37.80  cnf(c_0_206, negated_conjecture, (k3_subset_1(X1,k3_subset_1(X2,X2))=X1), inference(spm,[status(thm)],[c_0_199, c_0_200])).
% 37.61/37.80  cnf(c_0_207, negated_conjecture, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_180, c_0_189])).
% 37.61/37.80  cnf(c_0_208, plain, (k5_xboole_0(X1,X1)=X2|~r1_tarski(X2,k5_xboole_0(X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201, c_0_183]), c_0_160])])).
% 37.61/37.80  cnf(c_0_209, negated_conjecture, (r1_tarski(k3_xboole_0(esk5_0,k3_subset_1(esk3_0,esk5_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_202, c_0_203]), c_0_77])])).
% 37.61/37.80  cnf(c_0_210, negated_conjecture, (k5_xboole_0(esk3_0,esk4_0)=k3_subset_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_116]), c_0_30])])).
% 37.61/37.80  cnf(c_0_211, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(k1_zfmisc_1(esk5_0),k1_zfmisc_1(X2))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_204])).
% 37.61/37.80  cnf(c_0_212, negated_conjecture, (k5_xboole_0(X1,X1)=X1|~r1_tarski(X1,k3_subset_1(X2,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205, c_0_206]), c_0_207])])).
% 37.61/37.80  cnf(c_0_213, negated_conjecture, (k5_xboole_0(X1,X1)=k3_xboole_0(esk5_0,k3_subset_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_208, c_0_209])).
% 37.61/37.80  cnf(c_0_214, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_subset_1(esk3_0,esk4_0)))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196, c_0_116]), c_0_210])).
% 37.61/37.80  cnf(c_0_215, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X1,esk4_0)|~r1_tarski(esk5_0,X2)), inference(spm,[status(thm)],[c_0_211, c_0_48])).
% 37.61/37.80  cnf(c_0_216, negated_conjecture, (k5_xboole_0(X1,k3_subset_1(esk4_0,esk4_0))=X1), inference(rw,[status(thm)],[c_0_188, c_0_199])).
% 37.61/37.80  cnf(c_0_217, negated_conjecture, (k3_xboole_0(esk5_0,k3_subset_1(esk3_0,esk5_0))=X1|~r1_tarski(X1,k3_subset_1(X2,X2))), inference(rw,[status(thm)],[c_0_212, c_0_213])).
% 37.61/37.80  cnf(c_0_218, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,k3_subset_1(esk3_0,esk4_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_202, c_0_214]), c_0_77])])).
% 37.61/37.80  cnf(c_0_219, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,X1),X2)|~r1_tarski(esk5_0,X2)), inference(spm,[status(thm)],[c_0_215, c_0_77])).
% 37.61/37.80  cnf(c_0_220, negated_conjecture, (r1_xboole_0(X1,esk5_0)|~r1_tarski(X1,k3_subset_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_81, c_0_203])).
% 37.61/37.80  cnf(c_0_221, negated_conjecture, (k5_xboole_0(X1,k3_subset_1(X2,X2))=X1), inference(spm,[status(thm)],[c_0_216, c_0_200])).
% 37.61/37.80  cnf(c_0_222, negated_conjecture, (k3_xboole_0(esk5_0,k3_subset_1(esk3_0,esk5_0))=k3_xboole_0(esk4_0,k3_subset_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_217, c_0_218])).
% 37.61/37.80  cnf(c_0_223, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,X1),X2)|~r1_xboole_0(k3_xboole_0(esk4_0,X1),X3)|~r1_tarski(esk5_0,k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_56, c_0_219])).
% 37.61/37.80  cnf(c_0_224, negated_conjecture, (r1_xboole_0(k3_xboole_0(X1,k3_subset_1(esk3_0,esk5_0)),esk5_0)), inference(spm,[status(thm)],[c_0_220, c_0_102])).
% 37.61/37.80  cnf(c_0_225, negated_conjecture, (k5_xboole_0(X1,k5_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_221, c_0_183])).
% 37.61/37.80  cnf(c_0_226, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),k5_xboole_0(X3,k3_xboole_0(X3,X2)))|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X3)), inference(spm,[status(thm)],[c_0_169, c_0_109])).
% 37.61/37.80  cnf(c_0_227, negated_conjecture, (k3_xboole_0(esk4_0,k3_subset_1(esk3_0,esk4_0))=X1|~r1_tarski(X1,k3_subset_1(X2,X2))), inference(rw,[status(thm)],[c_0_217, c_0_222])).
% 37.61/37.80  cnf(c_0_228, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,k3_subset_1(esk3_0,esk5_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_223, c_0_224]), c_0_141])])).
% 37.61/37.80  cnf(c_0_229, negated_conjecture, (k5_xboole_0(X1,k3_xboole_0(esk5_0,k3_subset_1(esk3_0,esk5_0)))=X1), inference(rw,[status(thm)],[c_0_225, c_0_213])).
% 37.61/37.80  cnf(c_0_230, negated_conjecture, (~r1_tarski(esk4_0,esk5_0)|~r1_tarski(k3_subset_1(esk3_0,esk5_0),k3_subset_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 37.61/37.80  cnf(c_0_231, negated_conjecture, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(esk4_0,X1)),k3_subset_1(esk3_0,esk4_0))|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(esk4_0,X1)),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_226, c_0_116]), c_0_210])).
% 37.61/37.80  cnf(c_0_232, negated_conjecture, (k3_xboole_0(esk4_0,k3_subset_1(esk3_0,esk5_0))=k3_xboole_0(esk4_0,k3_subset_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_227, c_0_228])).
% 37.61/37.80  cnf(c_0_233, negated_conjecture, (k5_xboole_0(X1,k3_xboole_0(esk4_0,k3_subset_1(esk3_0,esk4_0)))=X1), inference(rw,[status(thm)],[c_0_229, c_0_222])).
% 37.61/37.80  cnf(c_0_234, negated_conjecture, (r1_tarski(k3_subset_1(esk3_0,esk5_0),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_110]), c_0_197])).
% 37.61/37.80  cnf(c_0_235, negated_conjecture, (~r1_tarski(k3_subset_1(esk3_0,esk5_0),k3_subset_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_230, c_0_97])])).
% 37.61/37.80  cnf(c_0_236, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_231, c_0_232]), c_0_233]), c_0_233]), c_0_234])]), c_0_235]), ['proof']).
% 37.61/37.80  # SZS output end CNFRefutation
% 37.61/37.80  # Proof object total steps             : 237
% 37.61/37.80  # Proof object clause steps            : 194
% 37.61/37.80  # Proof object formula steps           : 43
% 37.61/37.80  # Proof object conjectures             : 111
% 37.61/37.80  # Proof object clause conjectures      : 108
% 37.61/37.80  # Proof object formula conjectures     : 3
% 37.61/37.80  # Proof object initial clauses used    : 27
% 37.61/37.80  # Proof object initial formulas used   : 21
% 37.61/37.80  # Proof object generating inferences   : 145
% 37.61/37.80  # Proof object simplifying inferences  : 118
% 37.61/37.80  # Training examples: 0 positive, 0 negative
% 37.61/37.80  # Parsed axioms                        : 21
% 37.61/37.80  # Removed by relevancy pruning/SinE    : 0
% 37.61/37.80  # Initial clauses                      : 34
% 37.61/37.80  # Removed in clause preprocessing      : 1
% 37.61/37.80  # Initial clauses in saturation        : 33
% 37.61/37.80  # Processed clauses                    : 177766
% 37.61/37.80  # ...of these trivial                  : 1279
% 37.61/37.80  # ...subsumed                          : 160991
% 37.61/37.80  # ...remaining for further processing  : 15496
% 37.61/37.80  # Other redundant clauses eliminated   : 4
% 37.61/37.80  # Clauses deleted for lack of memory   : 584321
% 37.61/37.80  # Backward-subsumed                    : 2360
% 37.61/37.80  # Backward-rewritten                   : 1088
% 37.61/37.80  # Generated clauses                    : 3233185
% 37.61/37.80  # ...of the previous two non-trivial   : 3050913
% 37.61/37.80  # Contextual simplify-reflections      : 575
% 37.61/37.80  # Paramodulations                      : 3233003
% 37.61/37.80  # Factorizations                       : 178
% 37.61/37.80  # Equation resolutions                 : 4
% 37.61/37.80  # Propositional unsat checks           : 3
% 37.61/37.80  #    Propositional check models        : 0
% 37.61/37.80  #    Propositional check unsatisfiable : 0
% 37.61/37.80  #    Propositional clauses             : 0
% 37.61/37.80  #    Propositional clauses after purity: 0
% 37.61/37.80  #    Propositional unsat core size     : 0
% 37.61/37.80  #    Propositional preprocessing time  : 0.000
% 37.61/37.80  #    Propositional encoding time       : 3.337
% 37.61/37.80  #    Propositional solver time         : 0.841
% 37.61/37.80  #    Success case prop preproc time    : 0.000
% 37.61/37.80  #    Success case prop encoding time   : 0.000
% 37.61/37.80  #    Success case prop solver time     : 0.000
% 37.61/37.80  # Current number of processed clauses  : 12012
% 37.61/37.80  #    Positive orientable unit clauses  : 771
% 37.61/37.80  #    Positive unorientable unit clauses: 3
% 37.61/37.80  #    Negative unit clauses             : 547
% 37.61/37.80  #    Non-unit-clauses                  : 10691
% 37.61/37.80  # Current number of unprocessed clauses: 1776483
% 37.61/37.80  # ...number of literals in the above   : 8778683
% 37.61/37.80  # Current number of archived formulas  : 0
% 37.61/37.80  # Current number of archived clauses   : 3481
% 37.61/37.80  # Clause-clause subsumption calls (NU) : 26768510
% 37.61/37.80  # Rec. Clause-clause subsumption calls : 13739373
% 37.61/37.80  # Non-unit clause-clause subsumptions  : 78325
% 37.61/37.80  # Unit Clause-clause subsumption calls : 1011857
% 37.61/37.80  # Rewrite failures with RHS unbound    : 182
% 37.61/37.80  # BW rewrite match attempts            : 6701
% 37.61/37.80  # BW rewrite match successes           : 352
% 37.61/37.80  # Condensation attempts                : 0
% 37.61/37.80  # Condensation successes               : 0
% 37.61/37.80  # Termbank termtop insertions          : 103067493
% 37.66/37.88  
% 37.66/37.88  # -------------------------------------------------
% 37.66/37.88  # User time                : 36.488 s
% 37.66/37.88  # System time              : 1.046 s
% 37.66/37.88  # Total time               : 37.534 s
% 37.66/37.88  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
