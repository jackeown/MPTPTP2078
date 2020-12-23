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
% DateTime   : Thu Dec  3 10:45:23 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 196 expanded)
%              Number of clauses        :   56 (  94 expanded)
%              Number of leaves         :   16 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  224 ( 518 expanded)
%              Number of equality atoms :   60 ( 147 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t25_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_16,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( r2_hidden(X20,X17)
        | ~ r2_hidden(X20,X19)
        | X19 != k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | X19 != k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X21,X17)
        | r2_hidden(X21,X18)
        | r2_hidden(X21,X19)
        | X19 != k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk3_3(X22,X23,X24),X24)
        | ~ r2_hidden(esk3_3(X22,X23,X24),X22)
        | r2_hidden(esk3_3(X22,X23,X24),X23)
        | X24 = k4_xboole_0(X22,X23) )
      & ( r2_hidden(esk3_3(X22,X23,X24),X22)
        | r2_hidden(esk3_3(X22,X23,X24),X24)
        | X24 = k4_xboole_0(X22,X23) )
      & ( ~ r2_hidden(esk3_3(X22,X23,X24),X23)
        | r2_hidden(esk3_3(X22,X23,X24),X24)
        | X24 = k4_xboole_0(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_17,plain,(
    ! [X26,X27] : k4_xboole_0(X26,X27) = k5_xboole_0(X26,k3_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,plain,(
    ! [X41,X42] : k3_tarski(k2_tarski(X41,X42)) = k2_xboole_0(X41,X42) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X32,X33] : k1_enumset1(X32,X32,X33) = k2_tarski(X32,X33) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X46,X47] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(X46))
      | k3_subset_1(X46,X47) = k4_xboole_0(X46,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t25_subset_1])).

fof(c_0_24,plain,(
    ! [X49,X50,X51] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(X49))
      | ~ m1_subset_1(X51,k1_zfmisc_1(X49))
      | k4_subset_1(X49,X50,X51) = k2_xboole_0(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_25,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))
    & k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0)) != k2_subset_1(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_30,plain,(
    ! [X45] : k2_subset_1(X45) = X45 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_31,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_21])).

fof(c_0_35,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_36,plain,(
    ! [X34,X35,X36,X37,X38,X39] :
      ( ( ~ r2_hidden(X36,X35)
        | r1_tarski(X36,X34)
        | X35 != k1_zfmisc_1(X34) )
      & ( ~ r1_tarski(X37,X34)
        | r2_hidden(X37,X35)
        | X35 != k1_zfmisc_1(X34) )
      & ( ~ r2_hidden(esk4_2(X38,X39),X39)
        | ~ r1_tarski(esk4_2(X38,X39),X38)
        | X39 = k1_zfmisc_1(X38) )
      & ( r2_hidden(esk4_2(X38,X39),X39)
        | r1_tarski(esk4_2(X38,X39),X38)
        | X39 = k1_zfmisc_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_37,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0)) != k2_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k1_enumset1(X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k3_subset_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_43,plain,(
    ! [X43,X44] :
      ( ( ~ m1_subset_1(X44,X43)
        | r2_hidden(X44,X43)
        | v1_xboole_0(X43) )
      & ( ~ r2_hidden(X44,X43)
        | m1_subset_1(X44,X43)
        | v1_xboole_0(X43) )
      & ( ~ m1_subset_1(X44,X43)
        | v1_xboole_0(X44)
        | ~ v1_xboole_0(X43) )
      & ( ~ v1_xboole_0(X44)
        | m1_subset_1(X44,X43)
        | ~ v1_xboole_0(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_44,plain,(
    ! [X48] : ~ v1_xboole_0(k1_zfmisc_1(X48)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_45,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0)) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,plain,
    ( k4_subset_1(X1,X2,X3) = k4_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_48,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_49,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X3)
    | r2_hidden(esk2_2(k3_subset_1(X1,X2),X3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_50,plain,(
    ! [X30,X31] : k2_xboole_0(k3_xboole_0(X30,X31),k4_xboole_0(X30,X31)) = X30 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_51,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( k4_subset_1(X1,esk6_0,k3_subset_1(esk5_0,esk6_0)) != esk5_0
    | ~ m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(esk5_0))
    | ~ m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk5_0,esk6_0),X1)
    | r2_hidden(esk2_2(k3_subset_1(esk5_0,esk6_0),X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_47])).

cnf(c_0_61,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_62,plain,(
    ! [X28,X29] :
      ( ~ r1_tarski(X28,X29)
      | k3_xboole_0(X28,X29) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_63,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_47]),c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk6_0,esk6_0,k3_subset_1(esk5_0,esk6_0))) != esk5_0
    | ~ m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(esk5_0))
    | ~ m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_39])).

cnf(c_0_67,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_70,plain,
    ( k3_tarski(k1_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_32]),c_0_21])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk6_0,esk6_0,k3_subset_1(esk5_0,esk6_0))) != esk5_0
    | ~ m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(X1))
    | ~ r2_hidden(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,plain,
    ( k3_tarski(k1_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_subset_1(X1,X2))) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_34])).

cnf(c_0_77,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | r2_hidden(esk2_2(esk6_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_41])).

cnf(c_0_79,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | r2_hidden(esk2_2(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_41])).

cnf(c_0_80,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk6_0,esk6_0,k3_subset_1(esk5_0,esk6_0))) != esk5_0
    | ~ m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])])).

cnf(c_0_81,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k3_subset_1(X2,X1))) = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_78])).

cnf(c_0_83,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( ~ m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_47]),c_0_82])])).

cnf(c_0_85,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_34])).

cnf(c_0_86,negated_conjecture,
    ( ~ m1_subset_1(esk6_0,k1_zfmisc_1(X1))
    | ~ r2_hidden(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_67])).

cnf(c_0_87,plain,
    ( r2_hidden(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.59/0.81  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.59/0.81  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.59/0.81  #
% 0.59/0.81  # Preprocessing time       : 0.028 s
% 0.59/0.81  # Presaturation interreduction done
% 0.59/0.81  
% 0.59/0.81  # Proof found!
% 0.59/0.81  # SZS status Theorem
% 0.59/0.81  # SZS output start CNFRefutation
% 0.59/0.81  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.59/0.81  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.59/0.81  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.59/0.81  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.59/0.81  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.59/0.81  fof(t25_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 0.59/0.81  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.59/0.81  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.59/0.81  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.59/0.81  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.59/0.81  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.59/0.81  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.59/0.81  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.59/0.81  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.59/0.81  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.59/0.81  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.59/0.81  fof(c_0_16, plain, ![X17, X18, X19, X20, X21, X22, X23, X24]:((((r2_hidden(X20,X17)|~r2_hidden(X20,X19)|X19!=k4_xboole_0(X17,X18))&(~r2_hidden(X20,X18)|~r2_hidden(X20,X19)|X19!=k4_xboole_0(X17,X18)))&(~r2_hidden(X21,X17)|r2_hidden(X21,X18)|r2_hidden(X21,X19)|X19!=k4_xboole_0(X17,X18)))&((~r2_hidden(esk3_3(X22,X23,X24),X24)|(~r2_hidden(esk3_3(X22,X23,X24),X22)|r2_hidden(esk3_3(X22,X23,X24),X23))|X24=k4_xboole_0(X22,X23))&((r2_hidden(esk3_3(X22,X23,X24),X22)|r2_hidden(esk3_3(X22,X23,X24),X24)|X24=k4_xboole_0(X22,X23))&(~r2_hidden(esk3_3(X22,X23,X24),X23)|r2_hidden(esk3_3(X22,X23,X24),X24)|X24=k4_xboole_0(X22,X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.59/0.81  fof(c_0_17, plain, ![X26, X27]:k4_xboole_0(X26,X27)=k5_xboole_0(X26,k3_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.59/0.81  fof(c_0_18, plain, ![X41, X42]:k3_tarski(k2_tarski(X41,X42))=k2_xboole_0(X41,X42), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.59/0.81  fof(c_0_19, plain, ![X32, X33]:k1_enumset1(X32,X32,X33)=k2_tarski(X32,X33), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.59/0.81  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.59/0.81  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.59/0.81  fof(c_0_22, plain, ![X46, X47]:(~m1_subset_1(X47,k1_zfmisc_1(X46))|k3_subset_1(X46,X47)=k4_xboole_0(X46,X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.59/0.81  fof(c_0_23, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t25_subset_1])).
% 0.59/0.81  fof(c_0_24, plain, ![X49, X50, X51]:(~m1_subset_1(X50,k1_zfmisc_1(X49))|~m1_subset_1(X51,k1_zfmisc_1(X49))|k4_subset_1(X49,X50,X51)=k2_xboole_0(X50,X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.59/0.81  cnf(c_0_25, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.59/0.81  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.59/0.81  cnf(c_0_27, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.59/0.81  cnf(c_0_28, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.59/0.81  fof(c_0_29, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))&k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0))!=k2_subset_1(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.59/0.81  fof(c_0_30, plain, ![X45]:k2_subset_1(X45)=X45, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.59/0.81  cnf(c_0_31, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.59/0.81  cnf(c_0_32, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.59/0.81  cnf(c_0_33, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_27])).
% 0.59/0.81  cnf(c_0_34, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_28, c_0_21])).
% 0.59/0.81  fof(c_0_35, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.59/0.81  fof(c_0_36, plain, ![X34, X35, X36, X37, X38, X39]:(((~r2_hidden(X36,X35)|r1_tarski(X36,X34)|X35!=k1_zfmisc_1(X34))&(~r1_tarski(X37,X34)|r2_hidden(X37,X35)|X35!=k1_zfmisc_1(X34)))&((~r2_hidden(esk4_2(X38,X39),X39)|~r1_tarski(esk4_2(X38,X39),X38)|X39=k1_zfmisc_1(X38))&(r2_hidden(esk4_2(X38,X39),X39)|r1_tarski(esk4_2(X38,X39),X38)|X39=k1_zfmisc_1(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.59/0.81  cnf(c_0_37, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0))!=k2_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.59/0.81  cnf(c_0_38, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.59/0.81  cnf(c_0_39, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k1_enumset1(X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.59/0.81  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,k3_subset_1(X2,X3))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.59/0.81  cnf(c_0_41, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.59/0.81  cnf(c_0_42, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.59/0.81  fof(c_0_43, plain, ![X43, X44]:(((~m1_subset_1(X44,X43)|r2_hidden(X44,X43)|v1_xboole_0(X43))&(~r2_hidden(X44,X43)|m1_subset_1(X44,X43)|v1_xboole_0(X43)))&((~m1_subset_1(X44,X43)|v1_xboole_0(X44)|~v1_xboole_0(X43))&(~v1_xboole_0(X44)|m1_subset_1(X44,X43)|~v1_xboole_0(X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.59/0.81  fof(c_0_44, plain, ![X48]:~v1_xboole_0(k1_zfmisc_1(X48)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.59/0.81  cnf(c_0_45, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0))!=esk5_0), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.59/0.81  cnf(c_0_46, plain, (k4_subset_1(X1,X2,X3)=k4_subset_1(X4,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_39, c_0_39])).
% 0.59/0.81  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.59/0.81  fof(c_0_48, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.59/0.81  cnf(c_0_49, plain, (r1_tarski(k3_subset_1(X1,X2),X3)|r2_hidden(esk2_2(k3_subset_1(X1,X2),X3),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.59/0.81  fof(c_0_50, plain, ![X30, X31]:k2_xboole_0(k3_xboole_0(X30,X31),k4_xboole_0(X30,X31))=X30, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.59/0.81  cnf(c_0_51, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.59/0.81  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_42])).
% 0.59/0.81  cnf(c_0_53, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.59/0.81  cnf(c_0_54, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.59/0.81  cnf(c_0_55, negated_conjecture, (k4_subset_1(X1,esk6_0,k3_subset_1(esk5_0,esk6_0))!=esk5_0|~m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(esk5_0))|~m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(X1))|~m1_subset_1(esk6_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.59/0.81  cnf(c_0_56, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.59/0.81  cnf(c_0_57, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.59/0.81  cnf(c_0_58, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.59/0.81  cnf(c_0_59, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.59/0.81  cnf(c_0_60, negated_conjecture, (r1_tarski(k3_subset_1(esk5_0,esk6_0),X1)|r2_hidden(esk2_2(k3_subset_1(esk5_0,esk6_0),X1),esk5_0)), inference(spm,[status(thm)],[c_0_49, c_0_47])).
% 0.59/0.81  cnf(c_0_61, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.59/0.81  fof(c_0_62, plain, ![X28, X29]:(~r1_tarski(X28,X29)|k3_xboole_0(X28,X29)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.59/0.81  fof(c_0_63, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.59/0.81  cnf(c_0_64, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.59/0.81  cnf(c_0_65, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_47]), c_0_54])).
% 0.59/0.81  cnf(c_0_66, negated_conjecture, (k3_tarski(k1_enumset1(esk6_0,esk6_0,k3_subset_1(esk5_0,esk6_0)))!=esk5_0|~m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(esk5_0))|~m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(X1))|~m1_subset_1(esk6_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_55, c_0_39])).
% 0.59/0.81  cnf(c_0_67, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_56, c_0_57])).
% 0.59/0.81  cnf(c_0_68, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_58])).
% 0.59/0.81  cnf(c_0_69, negated_conjecture, (r1_tarski(k3_subset_1(esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.59/0.81  cnf(c_0_70, plain, (k3_tarski(k1_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_32]), c_0_21])).
% 0.59/0.81  cnf(c_0_71, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.59/0.81  cnf(c_0_72, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.59/0.81  cnf(c_0_73, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.59/0.81  cnf(c_0_74, negated_conjecture, (k3_tarski(k1_enumset1(esk6_0,esk6_0,k3_subset_1(esk5_0,esk6_0)))!=esk5_0|~m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(X1))|~m1_subset_1(esk6_0,k1_zfmisc_1(X1))|~r2_hidden(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.59/0.81  cnf(c_0_75, negated_conjecture, (r2_hidden(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.59/0.81  cnf(c_0_76, plain, (k3_tarski(k1_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_subset_1(X1,X2)))=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_70, c_0_34])).
% 0.59/0.81  cnf(c_0_77, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.59/0.81  cnf(c_0_78, negated_conjecture, (r1_tarski(esk6_0,X1)|r2_hidden(esk2_2(esk6_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_73, c_0_41])).
% 0.59/0.81  cnf(c_0_79, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|r2_hidden(esk2_2(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X1)), inference(spm,[status(thm)],[c_0_33, c_0_41])).
% 0.59/0.81  cnf(c_0_80, negated_conjecture, (k3_tarski(k1_enumset1(esk6_0,esk6_0,k3_subset_1(esk5_0,esk6_0)))!=esk5_0|~m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(X1))|~m1_subset_1(esk6_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75])])).
% 0.59/0.81  cnf(c_0_81, plain, (k3_tarski(k1_enumset1(X1,X1,k3_subset_1(X2,X1)))=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.59/0.81  cnf(c_0_82, negated_conjecture, (r1_tarski(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_59, c_0_78])).
% 0.59/0.81  cnf(c_0_83, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_59, c_0_79])).
% 0.59/0.81  cnf(c_0_84, negated_conjecture, (~m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(X1))|~m1_subset_1(esk6_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_47]), c_0_82])])).
% 0.59/0.81  cnf(c_0_85, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_83, c_0_34])).
% 0.59/0.81  cnf(c_0_86, negated_conjecture, (~m1_subset_1(esk6_0,k1_zfmisc_1(X1))|~r2_hidden(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_84, c_0_67])).
% 0.59/0.81  cnf(c_0_87, plain, (r2_hidden(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_68, c_0_85])).
% 0.59/0.81  cnf(c_0_88, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_47])]), ['proof']).
% 0.59/0.81  # SZS output end CNFRefutation
% 0.59/0.81  # Proof object total steps             : 89
% 0.59/0.81  # Proof object clause steps            : 56
% 0.59/0.81  # Proof object formula steps           : 33
% 0.59/0.81  # Proof object conjectures             : 20
% 0.59/0.81  # Proof object clause conjectures      : 17
% 0.59/0.81  # Proof object formula conjectures     : 3
% 0.59/0.81  # Proof object initial clauses used    : 21
% 0.59/0.81  # Proof object initial formulas used   : 16
% 0.59/0.81  # Proof object generating inferences   : 24
% 0.59/0.81  # Proof object simplifying inferences  : 21
% 0.59/0.81  # Training examples: 0 positive, 0 negative
% 0.59/0.81  # Parsed axioms                        : 16
% 0.59/0.81  # Removed by relevancy pruning/SinE    : 0
% 0.59/0.81  # Initial clauses                      : 31
% 0.59/0.81  # Removed in clause preprocessing      : 4
% 0.59/0.81  # Initial clauses in saturation        : 27
% 0.59/0.81  # Processed clauses                    : 2651
% 0.59/0.81  # ...of these trivial                  : 68
% 0.59/0.81  # ...subsumed                          : 1960
% 0.59/0.81  # ...remaining for further processing  : 623
% 0.59/0.81  # Other redundant clauses eliminated   : 15
% 0.59/0.81  # Clauses deleted for lack of memory   : 0
% 0.59/0.81  # Backward-subsumed                    : 104
% 0.59/0.81  # Backward-rewritten                   : 32
% 0.59/0.81  # Generated clauses                    : 22243
% 0.59/0.81  # ...of the previous two non-trivial   : 20566
% 0.59/0.81  # Contextual simplify-reflections      : 29
% 0.59/0.81  # Paramodulations                      : 22064
% 0.59/0.81  # Factorizations                       : 164
% 0.59/0.81  # Equation resolutions                 : 15
% 0.59/0.81  # Propositional unsat checks           : 0
% 0.59/0.81  #    Propositional check models        : 0
% 0.59/0.81  #    Propositional check unsatisfiable : 0
% 0.59/0.81  #    Propositional clauses             : 0
% 0.59/0.81  #    Propositional clauses after purity: 0
% 0.59/0.81  #    Propositional unsat core size     : 0
% 0.59/0.81  #    Propositional preprocessing time  : 0.000
% 0.59/0.81  #    Propositional encoding time       : 0.000
% 0.59/0.81  #    Propositional solver time         : 0.000
% 0.59/0.81  #    Success case prop preproc time    : 0.000
% 0.59/0.81  #    Success case prop encoding time   : 0.000
% 0.59/0.81  #    Success case prop solver time     : 0.000
% 0.59/0.81  # Current number of processed clauses  : 455
% 0.59/0.81  #    Positive orientable unit clauses  : 34
% 0.59/0.81  #    Positive unorientable unit clauses: 4
% 0.59/0.81  #    Negative unit clauses             : 15
% 0.59/0.81  #    Non-unit-clauses                  : 402
% 0.59/0.81  # Current number of unprocessed clauses: 17731
% 0.59/0.81  # ...number of literals in the above   : 91452
% 0.59/0.81  # Current number of archived formulas  : 0
% 0.59/0.81  # Current number of archived clauses   : 167
% 0.59/0.81  # Clause-clause subsumption calls (NU) : 22295
% 0.59/0.81  # Rec. Clause-clause subsumption calls : 12517
% 0.59/0.81  # Non-unit clause-clause subsumptions  : 1057
% 0.59/0.81  # Unit Clause-clause subsumption calls : 1644
% 0.59/0.81  # Rewrite failures with RHS unbound    : 106
% 0.59/0.81  # BW rewrite match attempts            : 319
% 0.59/0.81  # BW rewrite match successes           : 54
% 0.59/0.81  # Condensation attempts                : 0
% 0.59/0.81  # Condensation successes               : 0
% 0.59/0.81  # Termbank termtop insertions          : 423933
% 0.59/0.81  
% 0.59/0.81  # -------------------------------------------------
% 0.59/0.81  # User time                : 0.453 s
% 0.59/0.81  # System time              : 0.013 s
% 0.59/0.81  # Total time               : 0.466 s
% 0.59/0.81  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
