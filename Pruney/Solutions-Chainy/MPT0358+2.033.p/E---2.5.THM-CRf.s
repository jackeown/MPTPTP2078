%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:55 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 (5910 expanded)
%              Number of clauses        :   65 (2892 expanded)
%              Number of leaves         :   16 (1461 expanded)
%              Depth                    :   21
%              Number of atoms          :  229 (16679 expanded)
%              Number of equality atoms :   68 (4756 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(X2,k3_subset_1(X1,X2))
        <=> X2 = k1_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t38_subset_1])).

fof(c_0_17,plain,(
    ! [X41,X42,X43,X44,X45,X46] :
      ( ( ~ r2_hidden(X43,X42)
        | r1_tarski(X43,X41)
        | X42 != k1_zfmisc_1(X41) )
      & ( ~ r1_tarski(X44,X41)
        | r2_hidden(X44,X42)
        | X42 != k1_zfmisc_1(X41) )
      & ( ~ r2_hidden(esk5_2(X45,X46),X46)
        | ~ r1_tarski(esk5_2(X45,X46),X45)
        | X46 = k1_zfmisc_1(X45) )
      & ( r2_hidden(esk5_2(X45,X46),X46)
        | r1_tarski(esk5_2(X45,X46),X45)
        | X46 = k1_zfmisc_1(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_18,plain,(
    ! [X28,X29] :
      ( ( r1_tarski(X28,X29)
        | X28 != X29 )
      & ( r1_tarski(X29,X28)
        | X28 != X29 )
      & ( ~ r1_tarski(X28,X29)
        | ~ r1_tarski(X29,X28)
        | X28 = X29 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_19,plain,(
    ! [X48,X49] :
      ( ( ~ m1_subset_1(X49,X48)
        | r2_hidden(X49,X48)
        | v1_xboole_0(X48) )
      & ( ~ r2_hidden(X49,X48)
        | m1_subset_1(X49,X48)
        | v1_xboole_0(X48) )
      & ( ~ m1_subset_1(X49,X48)
        | v1_xboole_0(X49)
        | ~ v1_xboole_0(X48) )
      & ( ~ v1_xboole_0(X49)
        | m1_subset_1(X49,X48)
        | ~ v1_xboole_0(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_20,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk6_0))
    & ( ~ r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))
      | esk7_0 != k1_subset_1(esk6_0) )
    & ( r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))
      | esk7_0 = k1_subset_1(esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_21,plain,(
    ! [X53] : ~ v1_xboole_0(k1_zfmisc_1(X53)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X38,X39,X40] :
      ( ~ r1_tarski(X38,X39)
      | r1_xboole_0(X38,k4_xboole_0(X40,X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

fof(c_0_25,plain,(
    ! [X30,X31] : k4_xboole_0(X30,X31) = k5_xboole_0(X30,k3_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X51,X52] :
      ( ~ m1_subset_1(X52,k1_zfmisc_1(X51))
      | k3_subset_1(X51,X52) = k4_xboole_0(X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X32,X33] :
      ( ~ r1_tarski(X32,X33)
      | k3_xboole_0(X32,X33) = X32 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk7_0,k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_38,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_42,plain,(
    ! [X36,X37] :
      ( ( ~ r1_xboole_0(X36,X37)
        | k4_xboole_0(X36,X37) = X36 )
      & ( k4_xboole_0(X36,X37) != X36
        | r1_xboole_0(X36,X37) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_35])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_29])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_41,c_0_32])).

fof(c_0_48,plain,(
    ! [X34,X35] : k4_xboole_0(X34,k4_xboole_0(X34,X35)) = k3_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(esk7_0,k5_xboole_0(X1,k3_xboole_0(X1,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k3_xboole_0(esk7_0,esk6_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_44])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,X1) = k3_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

fof(c_0_53,plain,(
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

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_49,c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(esk7_0,k3_subset_1(esk7_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

fof(c_0_57,plain,(
    ! [X20,X21,X23,X24,X25] :
      ( ( r2_hidden(esk3_2(X20,X21),X20)
        | r1_xboole_0(X20,X21) )
      & ( r2_hidden(esk3_2(X20,X21),X21)
        | r1_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X25,X23)
        | ~ r2_hidden(X25,X24)
        | ~ r1_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_35]),c_0_35])).

cnf(c_0_60,negated_conjecture,
    ( k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,k3_subset_1(esk7_0,esk7_0))) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( k3_xboole_0(esk7_0,k3_subset_1(esk7_0,esk7_0)) = k3_subset_1(esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_47]),c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(X1,k3_subset_1(esk7_0,esk7_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_56])).

fof(c_0_65,plain,(
    ! [X26] :
      ( X26 = k1_xboole_0
      | r2_hidden(esk4_1(X26),X26) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_66,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_hidden(X1,k3_subset_1(esk7_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_69,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_67])).

cnf(c_0_71,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_72])).

fof(c_0_74,plain,(
    ! [X50] : k1_subset_1(X50) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_47]),c_0_52])).

cnf(c_0_76,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))
    | esk7_0 != k1_subset_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_78,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))
    | esk7_0 = k1_subset_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_80,negated_conjecture,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_52])).

cnf(c_0_81,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | ~ r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[c_0_79,c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( r1_xboole_0(esk7_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_76]),c_0_52]),c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(esk6_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,k1_xboole_0)) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk1_2(k1_xboole_0,k3_subset_1(esk6_0,k1_xboole_0)),k1_xboole_0)
    | r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_69])).

cnf(c_0_87,negated_conjecture,
    ( k3_subset_1(esk7_0,esk7_0) = k3_xboole_0(esk7_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_85]),c_0_47]),c_0_52])).

cnf(c_0_88,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_32])).

cnf(c_0_89,negated_conjecture,
    ( k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,esk7_0)) = k3_subset_1(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_28])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[c_0_86,c_0_70])).

cnf(c_0_91,negated_conjecture,
    ( k3_xboole_0(esk7_0,k3_xboole_0(esk7_0,k1_xboole_0)) = k3_xboole_0(esk7_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_87]),c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( ~ r2_hidden(X1,k3_xboole_0(esk7_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_67,c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( r1_xboole_0(esk7_0,k3_subset_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( k3_xboole_0(esk7_0,k3_subset_1(esk6_0,esk7_0)) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( k3_xboole_0(esk7_0,k1_xboole_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_68]),c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_90])])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_93]),c_0_94]),c_0_52]),c_0_87]),c_0_95]),c_0_96]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:25:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.21/0.47  # and selection function SelectCQIArEqFirst.
% 0.21/0.47  #
% 0.21/0.47  # Preprocessing time       : 0.028 s
% 0.21/0.47  # Presaturation interreduction done
% 0.21/0.47  
% 0.21/0.47  # Proof found!
% 0.21/0.47  # SZS status Theorem
% 0.21/0.47  # SZS output start CNFRefutation
% 0.21/0.47  fof(t38_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 0.21/0.47  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.21/0.47  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.47  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.21/0.47  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.21/0.47  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.21/0.47  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.47  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.21/0.47  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.21/0.47  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.21/0.47  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.47  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.21/0.47  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.21/0.47  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.21/0.47  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.47  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.21/0.47  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1)))), inference(assume_negation,[status(cth)],[t38_subset_1])).
% 0.21/0.47  fof(c_0_17, plain, ![X41, X42, X43, X44, X45, X46]:(((~r2_hidden(X43,X42)|r1_tarski(X43,X41)|X42!=k1_zfmisc_1(X41))&(~r1_tarski(X44,X41)|r2_hidden(X44,X42)|X42!=k1_zfmisc_1(X41)))&((~r2_hidden(esk5_2(X45,X46),X46)|~r1_tarski(esk5_2(X45,X46),X45)|X46=k1_zfmisc_1(X45))&(r2_hidden(esk5_2(X45,X46),X46)|r1_tarski(esk5_2(X45,X46),X45)|X46=k1_zfmisc_1(X45)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.21/0.47  fof(c_0_18, plain, ![X28, X29]:(((r1_tarski(X28,X29)|X28!=X29)&(r1_tarski(X29,X28)|X28!=X29))&(~r1_tarski(X28,X29)|~r1_tarski(X29,X28)|X28=X29)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.47  fof(c_0_19, plain, ![X48, X49]:(((~m1_subset_1(X49,X48)|r2_hidden(X49,X48)|v1_xboole_0(X48))&(~r2_hidden(X49,X48)|m1_subset_1(X49,X48)|v1_xboole_0(X48)))&((~m1_subset_1(X49,X48)|v1_xboole_0(X49)|~v1_xboole_0(X48))&(~v1_xboole_0(X49)|m1_subset_1(X49,X48)|~v1_xboole_0(X48)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.21/0.47  fof(c_0_20, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk6_0))&((~r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))|esk7_0!=k1_subset_1(esk6_0))&(r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))|esk7_0=k1_subset_1(esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.21/0.47  fof(c_0_21, plain, ![X53]:~v1_xboole_0(k1_zfmisc_1(X53)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.21/0.47  cnf(c_0_22, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.47  cnf(c_0_23, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.47  fof(c_0_24, plain, ![X38, X39, X40]:(~r1_tarski(X38,X39)|r1_xboole_0(X38,k4_xboole_0(X40,X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.21/0.47  fof(c_0_25, plain, ![X30, X31]:k4_xboole_0(X30,X31)=k5_xboole_0(X30,k3_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.47  cnf(c_0_26, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.47  cnf(c_0_27, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.47  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.47  cnf(c_0_29, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.47  fof(c_0_30, plain, ![X51, X52]:(~m1_subset_1(X52,k1_zfmisc_1(X51))|k3_subset_1(X51,X52)=k4_xboole_0(X51,X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.21/0.47  cnf(c_0_31, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_22])).
% 0.21/0.47  cnf(c_0_32, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_23])).
% 0.21/0.47  fof(c_0_33, plain, ![X32, X33]:(~r1_tarski(X32,X33)|k3_xboole_0(X32,X33)=X32), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.47  cnf(c_0_34, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.47  cnf(c_0_35, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.47  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_26])).
% 0.21/0.47  cnf(c_0_37, negated_conjecture, (r2_hidden(esk7_0,k1_zfmisc_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.21/0.47  cnf(c_0_38, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.47  cnf(c_0_39, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.47  cnf(c_0_40, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.47  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.47  fof(c_0_42, plain, ![X36, X37]:((~r1_xboole_0(X36,X37)|k4_xboole_0(X36,X37)=X36)&(k4_xboole_0(X36,X37)!=X36|r1_xboole_0(X36,X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.21/0.47  cnf(c_0_43, plain, (r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.47  cnf(c_0_44, negated_conjecture, (r1_tarski(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.21/0.47  cnf(c_0_45, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_38, c_0_35])).
% 0.21/0.47  cnf(c_0_46, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_29])).
% 0.21/0.47  cnf(c_0_47, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_41, c_0_32])).
% 0.21/0.47  fof(c_0_48, plain, ![X34, X35]:k4_xboole_0(X34,k4_xboole_0(X34,X35))=k3_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.47  cnf(c_0_49, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.47  cnf(c_0_50, negated_conjecture, (r1_xboole_0(esk7_0,k5_xboole_0(X1,k3_xboole_0(X1,esk6_0)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.47  cnf(c_0_51, negated_conjecture, (k3_xboole_0(esk7_0,esk6_0)=esk7_0), inference(spm,[status(thm)],[c_0_41, c_0_44])).
% 0.21/0.47  cnf(c_0_52, plain, (k5_xboole_0(X1,X1)=k3_subset_1(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.21/0.47  fof(c_0_53, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.21/0.47  cnf(c_0_54, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.47  cnf(c_0_55, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_49, c_0_35])).
% 0.21/0.47  cnf(c_0_56, negated_conjecture, (r1_xboole_0(esk7_0,k3_subset_1(esk7_0,esk7_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.21/0.47  fof(c_0_57, plain, ![X20, X21, X23, X24, X25]:(((r2_hidden(esk3_2(X20,X21),X20)|r1_xboole_0(X20,X21))&(r2_hidden(esk3_2(X20,X21),X21)|r1_xboole_0(X20,X21)))&(~r2_hidden(X25,X23)|~r2_hidden(X25,X24)|~r1_xboole_0(X23,X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.21/0.47  cnf(c_0_58, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.47  cnf(c_0_59, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_35]), c_0_35])).
% 0.21/0.47  cnf(c_0_60, negated_conjecture, (k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,k3_subset_1(esk7_0,esk7_0)))=esk7_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.21/0.47  cnf(c_0_61, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.21/0.47  cnf(c_0_62, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_58])).
% 0.21/0.47  cnf(c_0_63, negated_conjecture, (k3_xboole_0(esk7_0,k3_subset_1(esk7_0,esk7_0))=k3_subset_1(esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_47]), c_0_52])).
% 0.21/0.47  cnf(c_0_64, negated_conjecture, (~r2_hidden(X1,k3_subset_1(esk7_0,esk7_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_61, c_0_56])).
% 0.21/0.47  fof(c_0_65, plain, ![X26]:(X26=k1_xboole_0|r2_hidden(esk4_1(X26),X26)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.21/0.47  fof(c_0_66, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.47  cnf(c_0_67, negated_conjecture, (~r2_hidden(X1,k3_subset_1(esk7_0,esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.21/0.47  cnf(c_0_68, plain, (X1=k1_xboole_0|r2_hidden(esk4_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.21/0.47  cnf(c_0_69, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.21/0.47  cnf(c_0_70, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_67])).
% 0.21/0.47  cnf(c_0_71, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_31, c_0_69])).
% 0.21/0.47  cnf(c_0_72, negated_conjecture, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.21/0.47  cnf(c_0_73, negated_conjecture, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_72])).
% 0.21/0.47  fof(c_0_74, plain, ![X50]:k1_subset_1(X50)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.21/0.47  cnf(c_0_75, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(X1,X1)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_47]), c_0_52])).
% 0.21/0.47  cnf(c_0_76, negated_conjecture, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_73])).
% 0.21/0.47  cnf(c_0_77, negated_conjecture, (~r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))|esk7_0!=k1_subset_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.47  cnf(c_0_78, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.21/0.47  cnf(c_0_79, negated_conjecture, (r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))|esk7_0=k1_subset_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.47  cnf(c_0_80, negated_conjecture, (k3_subset_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_52])).
% 0.21/0.47  cnf(c_0_81, negated_conjecture, (esk7_0!=k1_xboole_0|~r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))), inference(rw,[status(thm)],[c_0_77, c_0_78])).
% 0.21/0.47  cnf(c_0_82, negated_conjecture, (esk7_0=k1_xboole_0|r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))), inference(rw,[status(thm)],[c_0_79, c_0_78])).
% 0.21/0.47  cnf(c_0_83, negated_conjecture, (r1_xboole_0(esk7_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_76]), c_0_52]), c_0_80])).
% 0.21/0.47  cnf(c_0_84, negated_conjecture, (r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))|~r1_tarski(k1_xboole_0,k3_subset_1(esk6_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.21/0.47  cnf(c_0_85, negated_conjecture, (k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,k1_xboole_0))=esk7_0), inference(spm,[status(thm)],[c_0_55, c_0_83])).
% 0.21/0.47  cnf(c_0_86, negated_conjecture, (r2_hidden(esk1_2(k1_xboole_0,k3_subset_1(esk6_0,k1_xboole_0)),k1_xboole_0)|r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_84, c_0_69])).
% 0.21/0.47  cnf(c_0_87, negated_conjecture, (k3_subset_1(esk7_0,esk7_0)=k3_xboole_0(esk7_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_85]), c_0_47]), c_0_52])).
% 0.21/0.47  cnf(c_0_88, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_43, c_0_32])).
% 0.21/0.47  cnf(c_0_89, negated_conjecture, (k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,esk7_0))=k3_subset_1(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_45, c_0_28])).
% 0.21/0.47  cnf(c_0_90, negated_conjecture, (r1_tarski(esk7_0,k3_subset_1(esk6_0,esk7_0))), inference(sr,[status(thm)],[c_0_86, c_0_70])).
% 0.21/0.47  cnf(c_0_91, negated_conjecture, (k3_xboole_0(esk7_0,k3_xboole_0(esk7_0,k1_xboole_0))=k3_xboole_0(esk7_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_87]), c_0_87])).
% 0.21/0.47  cnf(c_0_92, negated_conjecture, (~r2_hidden(X1,k3_xboole_0(esk7_0,k1_xboole_0))), inference(rw,[status(thm)],[c_0_67, c_0_87])).
% 0.21/0.47  cnf(c_0_93, negated_conjecture, (r1_xboole_0(esk7_0,k3_subset_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.21/0.47  cnf(c_0_94, negated_conjecture, (k3_xboole_0(esk7_0,k3_subset_1(esk6_0,esk7_0))=esk7_0), inference(spm,[status(thm)],[c_0_41, c_0_90])).
% 0.21/0.47  cnf(c_0_95, negated_conjecture, (k3_xboole_0(esk7_0,k1_xboole_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_68]), c_0_92])).
% 0.21/0.47  cnf(c_0_96, negated_conjecture, (esk7_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_90])])).
% 0.21/0.47  cnf(c_0_97, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_93]), c_0_94]), c_0_52]), c_0_87]), c_0_95]), c_0_96]), ['proof']).
% 0.21/0.47  # SZS output end CNFRefutation
% 0.21/0.47  # Proof object total steps             : 98
% 0.21/0.47  # Proof object clause steps            : 65
% 0.21/0.47  # Proof object formula steps           : 33
% 0.21/0.47  # Proof object conjectures             : 36
% 0.21/0.47  # Proof object clause conjectures      : 33
% 0.21/0.47  # Proof object formula conjectures     : 3
% 0.21/0.47  # Proof object initial clauses used    : 20
% 0.21/0.47  # Proof object initial formulas used   : 16
% 0.21/0.47  # Proof object generating inferences   : 31
% 0.21/0.47  # Proof object simplifying inferences  : 37
% 0.21/0.47  # Training examples: 0 positive, 0 negative
% 0.21/0.47  # Parsed axioms                        : 16
% 0.21/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.47  # Initial clauses                      : 36
% 0.21/0.47  # Removed in clause preprocessing      : 2
% 0.21/0.47  # Initial clauses in saturation        : 34
% 0.21/0.47  # Processed clauses                    : 751
% 0.21/0.47  # ...of these trivial                  : 106
% 0.21/0.47  # ...subsumed                          : 252
% 0.21/0.47  # ...remaining for further processing  : 393
% 0.21/0.47  # Other redundant clauses eliminated   : 60
% 0.21/0.47  # Clauses deleted for lack of memory   : 0
% 0.21/0.47  # Backward-subsumed                    : 9
% 0.21/0.47  # Backward-rewritten                   : 65
% 0.21/0.47  # Generated clauses                    : 8494
% 0.21/0.47  # ...of the previous two non-trivial   : 5575
% 0.21/0.47  # Contextual simplify-reflections      : 1
% 0.21/0.47  # Paramodulations                      : 8433
% 0.21/0.47  # Factorizations                       : 0
% 0.21/0.47  # Equation resolutions                 : 60
% 0.21/0.47  # Propositional unsat checks           : 0
% 0.21/0.47  #    Propositional check models        : 0
% 0.21/0.47  #    Propositional check unsatisfiable : 0
% 0.21/0.47  #    Propositional clauses             : 0
% 0.21/0.47  #    Propositional clauses after purity: 0
% 0.21/0.47  #    Propositional unsat core size     : 0
% 0.21/0.47  #    Propositional preprocessing time  : 0.000
% 0.21/0.47  #    Propositional encoding time       : 0.000
% 0.21/0.47  #    Propositional solver time         : 0.000
% 0.21/0.47  #    Success case prop preproc time    : 0.000
% 0.21/0.47  #    Success case prop encoding time   : 0.000
% 0.21/0.47  #    Success case prop solver time     : 0.000
% 0.21/0.47  # Current number of processed clauses  : 278
% 0.21/0.47  #    Positive orientable unit clauses  : 89
% 0.21/0.47  #    Positive unorientable unit clauses: 0
% 0.21/0.47  #    Negative unit clauses             : 45
% 0.21/0.47  #    Non-unit-clauses                  : 144
% 0.21/0.47  # Current number of unprocessed clauses: 4662
% 0.21/0.47  # ...number of literals in the above   : 12591
% 0.21/0.47  # Current number of archived formulas  : 0
% 0.21/0.47  # Current number of archived clauses   : 110
% 0.21/0.47  # Clause-clause subsumption calls (NU) : 3660
% 0.21/0.47  # Rec. Clause-clause subsumption calls : 3286
% 0.21/0.47  # Non-unit clause-clause subsumptions  : 150
% 0.21/0.47  # Unit Clause-clause subsumption calls : 742
% 0.21/0.47  # Rewrite failures with RHS unbound    : 0
% 0.21/0.47  # BW rewrite match attempts            : 47
% 0.21/0.47  # BW rewrite match successes           : 24
% 0.21/0.47  # Condensation attempts                : 0
% 0.21/0.47  # Condensation successes               : 0
% 0.21/0.47  # Termbank termtop insertions          : 90643
% 0.21/0.47  
% 0.21/0.47  # -------------------------------------------------
% 0.21/0.47  # User time                : 0.119 s
% 0.21/0.47  # System time              : 0.008 s
% 0.21/0.47  # Total time               : 0.127 s
% 0.21/0.47  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
