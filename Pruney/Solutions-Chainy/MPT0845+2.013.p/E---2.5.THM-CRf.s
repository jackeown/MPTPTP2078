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
% DateTime   : Thu Dec  3 10:58:55 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 110 expanded)
%              Number of clauses        :   40 (  49 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  162 ( 256 expanded)
%              Number of equality atoms :   36 (  52 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t1_mcart_1,conjecture,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(t50_subset_1,axiom,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ( ~ r2_hidden(X3,X2)
               => r2_hidden(X3,k3_subset_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(c_0_17,plain,(
    ! [X39,X40] : k1_setfam_1(k2_tarski(X39,X40)) = k3_xboole_0(X39,X40) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_18,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X15,X16] : k4_xboole_0(X15,X16) = k5_xboole_0(X15,k3_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X44,X45] :
      ( ~ r2_hidden(X44,X45)
      | ~ r1_tarski(X45,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_23,plain,(
    ! [X18] : r1_tarski(k1_xboole_0,X18) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_24,plain,(
    ! [X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | k3_subset_1(X31,X32) = k4_xboole_0(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_27,plain,(
    ! [X22,X23,X24] : k2_enumset1(X22,X22,X23,X24) = k1_enumset1(X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X17] : k3_xboole_0(X17,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1] :
        ~ ( X1 != k1_xboole_0
          & ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r1_xboole_0(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t1_mcart_1])).

fof(c_0_30,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_31,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r2_hidden(esk2_2(X9,X10),X9)
        | r1_xboole_0(X9,X10) )
      & ( r2_hidden(esk2_2(X9,X10),X10)
        | r1_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_32,plain,(
    ! [X36,X37,X38] :
      ( X36 = k1_xboole_0
      | ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | ~ m1_subset_1(X38,X36)
      | r2_hidden(X38,X37)
      | r2_hidden(X38,k3_subset_1(X36,X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_subset_1])])])])).

fof(c_0_33,plain,(
    ! [X35] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X35)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_40,plain,(
    ! [X19] : k5_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_41,plain,(
    ! [X25,X26,X28] :
      ( ( r2_hidden(esk3_2(X25,X26),X26)
        | ~ r2_hidden(X25,X26) )
      & ( ~ r2_hidden(X28,X26)
        | ~ r2_hidden(X28,esk3_2(X25,X26))
        | ~ r2_hidden(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

fof(c_0_42,negated_conjecture,(
    ! [X47] :
      ( esk5_0 != k1_xboole_0
      & ( ~ r2_hidden(X47,esk5_0)
        | ~ r1_xboole_0(X47,esk5_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])])).

cnf(c_0_43,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_45,plain,(
    ! [X29,X30] :
      ( ( ~ m1_subset_1(X30,X29)
        | r2_hidden(X30,X29)
        | v1_xboole_0(X29) )
      & ( ~ r2_hidden(X30,X29)
        | m1_subset_1(X30,X29)
        | v1_xboole_0(X29) )
      & ( ~ m1_subset_1(X30,X29)
        | v1_xboole_0(X30)
        | ~ v1_xboole_0(X29) )
      & ( ~ v1_xboole_0(X30)
        | m1_subset_1(X30,X29)
        | ~ v1_xboole_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_46,plain,(
    ! [X33] : m1_subset_1(esk4_1(X33),X33) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X3,X2)
    | r2_hidden(X3,k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_50,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_51,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_26]),c_0_38])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk3_2(X3,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ r1_xboole_0(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_56,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( m1_subset_1(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k3_subset_1(X1,k1_xboole_0))
    | ~ m1_subset_1(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_59,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_48])])).

cnf(c_0_60,plain,
    ( r1_xboole_0(esk3_2(X1,X2),X3)
    | ~ r2_hidden(esk2_2(esk3_2(X1,X2),X3),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_44])).

cnf(c_0_61,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,plain,
    ( v1_xboole_0(esk4_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,plain,
    ( r1_xboole_0(esk3_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(esk4_1(X1),esk5_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_57])).

cnf(c_0_70,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_65]),c_0_66])).

cnf(c_0_72,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_57])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:51:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.14/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.14/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.14/0.38  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.14/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.38  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.14/0.38  fof(t1_mcart_1, conjecture, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 0.14/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.14/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.14/0.38  fof(t50_subset_1, axiom, ![X1]:(X1!=k1_xboole_0=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,X1)=>(~(r2_hidden(X3,X2))=>r2_hidden(X3,k3_subset_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 0.14/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.14/0.38  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.14/0.38  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 0.14/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.14/0.38  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.14/0.38  fof(c_0_17, plain, ![X39, X40]:k1_setfam_1(k2_tarski(X39,X40))=k3_xboole_0(X39,X40), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.38  fof(c_0_18, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.38  fof(c_0_19, plain, ![X15, X16]:k4_xboole_0(X15,X16)=k5_xboole_0(X15,k3_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.14/0.38  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  fof(c_0_22, plain, ![X44, X45]:(~r2_hidden(X44,X45)|~r1_tarski(X45,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.14/0.38  fof(c_0_23, plain, ![X18]:r1_tarski(k1_xboole_0,X18), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.14/0.38  fof(c_0_24, plain, ![X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(X31))|k3_subset_1(X31,X32)=k4_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.14/0.38  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  cnf(c_0_26, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.38  fof(c_0_27, plain, ![X22, X23, X24]:k2_enumset1(X22,X22,X23,X24)=k1_enumset1(X22,X23,X24), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.38  fof(c_0_28, plain, ![X17]:k3_xboole_0(X17,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.14/0.38  fof(c_0_29, negated_conjecture, ~(![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1)))))), inference(assume_negation,[status(cth)],[t1_mcart_1])).
% 0.14/0.38  fof(c_0_30, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.14/0.38  fof(c_0_31, plain, ![X9, X10, X12, X13, X14]:(((r2_hidden(esk2_2(X9,X10),X9)|r1_xboole_0(X9,X10))&(r2_hidden(esk2_2(X9,X10),X10)|r1_xboole_0(X9,X10)))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|~r1_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.14/0.38  fof(c_0_32, plain, ![X36, X37, X38]:(X36=k1_xboole_0|(~m1_subset_1(X37,k1_zfmisc_1(X36))|(~m1_subset_1(X38,X36)|(r2_hidden(X38,X37)|r2_hidden(X38,k3_subset_1(X36,X37)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_subset_1])])])])).
% 0.14/0.38  fof(c_0_33, plain, ![X35]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X35)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.14/0.38  cnf(c_0_34, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_35, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.38  cnf(c_0_36, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.38  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.38  cnf(c_0_39, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  fof(c_0_40, plain, ![X19]:k5_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.14/0.38  fof(c_0_41, plain, ![X25, X26, X28]:((r2_hidden(esk3_2(X25,X26),X26)|~r2_hidden(X25,X26))&(~r2_hidden(X28,X26)|~r2_hidden(X28,esk3_2(X25,X26))|~r2_hidden(X25,X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 0.14/0.38  fof(c_0_42, negated_conjecture, ![X47]:(esk5_0!=k1_xboole_0&(~r2_hidden(X47,esk5_0)|~r1_xboole_0(X47,esk5_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])])).
% 0.14/0.38  cnf(c_0_43, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_44, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.38  fof(c_0_45, plain, ![X29, X30]:(((~m1_subset_1(X30,X29)|r2_hidden(X30,X29)|v1_xboole_0(X29))&(~r2_hidden(X30,X29)|m1_subset_1(X30,X29)|v1_xboole_0(X29)))&((~m1_subset_1(X30,X29)|v1_xboole_0(X30)|~v1_xboole_0(X29))&(~v1_xboole_0(X30)|m1_subset_1(X30,X29)|~v1_xboole_0(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.14/0.38  fof(c_0_46, plain, ![X33]:m1_subset_1(esk4_1(X33),X33), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.14/0.38  cnf(c_0_47, plain, (X1=k1_xboole_0|r2_hidden(X3,X2)|r2_hidden(X3,k3_subset_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.38  cnf(c_0_48, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  cnf(c_0_49, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.38  cnf(c_0_50, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.14/0.38  cnf(c_0_51, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_26]), c_0_38])).
% 0.14/0.38  cnf(c_0_52, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.14/0.38  cnf(c_0_53, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,esk3_2(X3,X2))|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, (~r2_hidden(X1,esk5_0)|~r1_xboole_0(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.14/0.38  cnf(c_0_55, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.14/0.38  cnf(c_0_56, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.14/0.38  cnf(c_0_57, plain, (m1_subset_1(esk4_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.14/0.38  cnf(c_0_58, plain, (X1=k1_xboole_0|r2_hidden(X2,k3_subset_1(X1,k1_xboole_0))|~m1_subset_1(X2,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.14/0.38  cnf(c_0_59, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_48])])).
% 0.14/0.38  cnf(c_0_60, plain, (r1_xboole_0(esk3_2(X1,X2),X3)|~r2_hidden(esk2_2(esk3_2(X1,X2),X3),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_53, c_0_44])).
% 0.14/0.38  cnf(c_0_61, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.38  cnf(c_0_62, negated_conjecture, (~r2_hidden(X1,esk5_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.14/0.38  cnf(c_0_63, plain, (v1_xboole_0(esk4_1(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.14/0.38  cnf(c_0_64, plain, (X1=k1_xboole_0|r2_hidden(X2,X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.14/0.38  cnf(c_0_65, plain, (r1_xboole_0(esk3_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.14/0.38  cnf(c_0_66, plain, (r2_hidden(esk3_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.38  cnf(c_0_67, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.14/0.38  cnf(c_0_68, negated_conjecture, (~r2_hidden(esk4_1(X1),esk5_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.14/0.38  cnf(c_0_69, plain, (X1=k1_xboole_0|r2_hidden(esk4_1(X1),X1)), inference(spm,[status(thm)],[c_0_64, c_0_57])).
% 0.14/0.38  cnf(c_0_70, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.14/0.38  cnf(c_0_71, negated_conjecture, (~r2_hidden(X1,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_65]), c_0_66])).
% 0.14/0.38  cnf(c_0_72, plain, (r2_hidden(esk4_1(X1),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_67, c_0_57])).
% 0.14/0.38  cnf(c_0_73, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 0.14/0.38  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 75
% 0.14/0.38  # Proof object clause steps            : 40
% 0.14/0.38  # Proof object formula steps           : 35
% 0.14/0.38  # Proof object conjectures             : 10
% 0.14/0.38  # Proof object clause conjectures      : 7
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 21
% 0.14/0.38  # Proof object initial formulas used   : 17
% 0.14/0.38  # Proof object generating inferences   : 14
% 0.14/0.38  # Proof object simplifying inferences  : 14
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 18
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 26
% 0.14/0.38  # Removed in clause preprocessing      : 4
% 0.14/0.38  # Initial clauses in saturation        : 22
% 0.14/0.38  # Processed clauses                    : 140
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 37
% 0.14/0.38  # ...remaining for further processing  : 103
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 2
% 0.14/0.38  # Backward-rewritten                   : 4
% 0.14/0.38  # Generated clauses                    : 198
% 0.14/0.38  # ...of the previous two non-trivial   : 161
% 0.14/0.38  # Contextual simplify-reflections      : 3
% 0.14/0.38  # Paramodulations                      : 198
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 75
% 0.14/0.38  #    Positive orientable unit clauses  : 10
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 5
% 0.14/0.38  #    Non-unit-clauses                  : 60
% 0.14/0.38  # Current number of unprocessed clauses: 63
% 0.14/0.38  # ...number of literals in the above   : 199
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 32
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 491
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 395
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 28
% 0.14/0.38  # Unit Clause-clause subsumption calls : 15
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 2
% 0.14/0.38  # BW rewrite match successes           : 2
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 4161
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.034 s
% 0.14/0.38  # System time              : 0.003 s
% 0.14/0.38  # Total time               : 0.037 s
% 0.14/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
