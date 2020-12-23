%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:36 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 173 expanded)
%              Number of clauses        :   48 (  77 expanded)
%              Number of leaves         :   18 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  160 ( 433 expanded)
%              Number of equality atoms :   59 ( 113 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ! [X4] :
              ( m1_subset_1(X4,k1_zfmisc_1(X1))
             => ( ( r1_tarski(X2,X3)
                  & r1_xboole_0(X4,X3) )
               => r1_tarski(X2,k3_subset_1(X1,X4)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t73_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( ( r1_tarski(X2,X3)
                    & r1_xboole_0(X4,X3) )
                 => r1_tarski(X2,k3_subset_1(X1,X4)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t47_subset_1])).

fof(c_0_19,plain,(
    ! [X30,X31,X32,X33,X34,X35] :
      ( ( ~ r2_hidden(X32,X31)
        | r1_tarski(X32,X30)
        | X31 != k1_zfmisc_1(X30) )
      & ( ~ r1_tarski(X33,X30)
        | r2_hidden(X33,X31)
        | X31 != k1_zfmisc_1(X30) )
      & ( ~ r2_hidden(esk1_2(X34,X35),X35)
        | ~ r1_tarski(esk1_2(X34,X35),X34)
        | X35 = k1_zfmisc_1(X34) )
      & ( r2_hidden(esk1_2(X34,X35),X35)
        | r1_tarski(esk1_2(X34,X35),X34)
        | X35 = k1_zfmisc_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_20,plain,(
    ! [X37,X38] :
      ( ( ~ m1_subset_1(X38,X37)
        | r2_hidden(X38,X37)
        | v1_xboole_0(X37) )
      & ( ~ r2_hidden(X38,X37)
        | m1_subset_1(X38,X37)
        | v1_xboole_0(X37) )
      & ( ~ m1_subset_1(X38,X37)
        | v1_xboole_0(X38)
        | ~ v1_xboole_0(X37) )
      & ( ~ v1_xboole_0(X38)
        | m1_subset_1(X38,X37)
        | ~ v1_xboole_0(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))
    & r1_tarski(esk3_0,esk4_0)
    & r1_xboole_0(esk5_0,esk4_0)
    & ~ r1_tarski(esk3_0,k3_subset_1(esk2_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_22,plain,(
    ! [X41] : ~ v1_xboole_0(k1_zfmisc_1(X41)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k3_xboole_0(X19,X20) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

fof(c_0_30,plain,(
    ! [X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X39))
      | k3_subset_1(X39,X40) = k4_xboole_0(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_31,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(X14,k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk5_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_34,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_35,plain,(
    ! [X25,X26] : k2_xboole_0(k3_xboole_0(X25,X26),k4_xboole_0(X25,X26)) = X25 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_36,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk2_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_40,plain,(
    ! [X27,X28,X29] :
      ( ~ r1_tarski(X27,k2_xboole_0(X28,X29))
      | ~ r1_xboole_0(X27,X29)
      | r1_tarski(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).

fof(c_0_41,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_42,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk5_0) = esk5_0 ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_42,c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk5_0) = k3_subset_1(esk2_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_25]),c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_50,plain,(
    ! [X10,X11] :
      ( ~ r1_xboole_0(X10,X11)
      | r1_xboole_0(X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( k2_xboole_0(esk5_0,k3_subset_1(esk2_0,esk5_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_44]),c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_49]),c_0_26])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_56,plain,(
    ! [X22] : k4_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_57,plain,(
    ! [X16,X17,X18] : k3_xboole_0(k3_xboole_0(X16,X17),X18) = k3_xboole_0(X16,k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk2_0,esk5_0))
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_62,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k4_xboole_0(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_64,plain,(
    ! [X21] : k3_xboole_0(X21,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_65,plain,(
    ! [X12,X13] :
      ( ( k4_xboole_0(X12,X13) != k1_xboole_0
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | k4_xboole_0(X12,X13) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_66,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk4_0,k3_subset_1(esk2_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

cnf(c_0_69,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_63,c_0_37])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_72,plain,(
    ! [X9] : k3_xboole_0(X9,X9) = X9 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_xboole_0(esk4_0,X1)) = k3_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_subset_1(esk2_0,esk5_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_67,c_0_39])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_37]),c_0_37])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_79,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_73,c_0_37])).

cnf(c_0_81,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_subset_1(esk2_0,esk5_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_39]),c_0_76])).

cnf(c_0_82,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_71]),c_0_78]),c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k3_subset_1(esk2_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])]),c_0_83]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:00:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S04DN
% 0.14/0.39  # and selection function SelectNewComplex.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.027 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t47_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_xboole_0(X4,X3))=>r1_tarski(X2,k3_subset_1(X1,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_subset_1)).
% 0.14/0.39  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.14/0.39  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.14/0.39  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.14/0.39  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.14/0.39  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.14/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.14/0.39  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.14/0.39  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.14/0.39  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 0.14/0.39  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.14/0.39  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.14/0.39  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.14/0.39  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.14/0.39  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.14/0.39  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.14/0.39  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.14/0.39  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.14/0.39  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_xboole_0(X4,X3))=>r1_tarski(X2,k3_subset_1(X1,X4))))))), inference(assume_negation,[status(cth)],[t47_subset_1])).
% 0.14/0.39  fof(c_0_19, plain, ![X30, X31, X32, X33, X34, X35]:(((~r2_hidden(X32,X31)|r1_tarski(X32,X30)|X31!=k1_zfmisc_1(X30))&(~r1_tarski(X33,X30)|r2_hidden(X33,X31)|X31!=k1_zfmisc_1(X30)))&((~r2_hidden(esk1_2(X34,X35),X35)|~r1_tarski(esk1_2(X34,X35),X34)|X35=k1_zfmisc_1(X34))&(r2_hidden(esk1_2(X34,X35),X35)|r1_tarski(esk1_2(X34,X35),X34)|X35=k1_zfmisc_1(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.14/0.39  fof(c_0_20, plain, ![X37, X38]:(((~m1_subset_1(X38,X37)|r2_hidden(X38,X37)|v1_xboole_0(X37))&(~r2_hidden(X38,X37)|m1_subset_1(X38,X37)|v1_xboole_0(X37)))&((~m1_subset_1(X38,X37)|v1_xboole_0(X38)|~v1_xboole_0(X37))&(~v1_xboole_0(X38)|m1_subset_1(X38,X37)|~v1_xboole_0(X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.14/0.39  fof(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))&((r1_tarski(esk3_0,esk4_0)&r1_xboole_0(esk5_0,esk4_0))&~r1_tarski(esk3_0,k3_subset_1(esk2_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.14/0.39  fof(c_0_22, plain, ![X41]:~v1_xboole_0(k1_zfmisc_1(X41)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.14/0.39  cnf(c_0_23, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  cnf(c_0_24, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.39  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  cnf(c_0_26, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  fof(c_0_27, plain, ![X19, X20]:(~r1_tarski(X19,X20)|k3_xboole_0(X19,X20)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.14/0.39  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_23])).
% 0.14/0.39  cnf(c_0_29, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.14/0.39  fof(c_0_30, plain, ![X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(X39))|k3_subset_1(X39,X40)=k4_xboole_0(X39,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.14/0.39  fof(c_0_31, plain, ![X14, X15]:k4_xboole_0(X14,X15)=k5_xboole_0(X14,k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.14/0.39  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.39  cnf(c_0_33, negated_conjecture, (r1_tarski(esk5_0,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.39  fof(c_0_34, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.14/0.39  fof(c_0_35, plain, ![X25, X26]:k2_xboole_0(k3_xboole_0(X25,X26),k4_xboole_0(X25,X26))=X25, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.14/0.39  cnf(c_0_36, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.39  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.39  cnf(c_0_38, negated_conjecture, (k3_xboole_0(esk5_0,esk2_0)=esk5_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.14/0.39  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.39  fof(c_0_40, plain, ![X27, X28, X29]:(~r1_tarski(X27,k2_xboole_0(X28,X29))|~r1_xboole_0(X27,X29)|r1_tarski(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 0.14/0.39  fof(c_0_41, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.14/0.39  cnf(c_0_42, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.39  cnf(c_0_43, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.39  cnf(c_0_44, negated_conjecture, (k3_xboole_0(esk2_0,esk5_0)=esk5_0), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.14/0.39  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.14/0.39  cnf(c_0_46, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.39  cnf(c_0_47, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_42, c_0_37])).
% 0.14/0.39  cnf(c_0_48, negated_conjecture, (k5_xboole_0(esk2_0,esk5_0)=k3_subset_1(esk2_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_25]), c_0_44])).
% 0.14/0.39  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  fof(c_0_50, plain, ![X10, X11]:(~r1_xboole_0(X10,X11)|r1_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.14/0.39  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.14/0.39  cnf(c_0_52, negated_conjecture, (k2_xboole_0(esk5_0,k3_subset_1(esk2_0,esk5_0))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_44]), c_0_48])).
% 0.14/0.39  cnf(c_0_53, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_49]), c_0_26])).
% 0.14/0.39  cnf(c_0_54, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.14/0.39  cnf(c_0_55, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  fof(c_0_56, plain, ![X22]:k4_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.14/0.39  fof(c_0_57, plain, ![X16, X17, X18]:k3_xboole_0(k3_xboole_0(X16,X17),X18)=k3_xboole_0(X16,k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.14/0.39  cnf(c_0_58, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  cnf(c_0_59, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk2_0,esk5_0))|~r1_tarski(X1,esk2_0)|~r1_xboole_0(X1,esk5_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.14/0.39  cnf(c_0_60, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_53])).
% 0.14/0.39  cnf(c_0_61, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.14/0.39  fof(c_0_62, plain, ![X23, X24]:k4_xboole_0(X23,k4_xboole_0(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.14/0.39  cnf(c_0_63, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.14/0.39  fof(c_0_64, plain, ![X21]:k3_xboole_0(X21,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.14/0.39  fof(c_0_65, plain, ![X12, X13]:((k4_xboole_0(X12,X13)!=k1_xboole_0|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|k4_xboole_0(X12,X13)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.14/0.39  cnf(c_0_66, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.14/0.39  cnf(c_0_67, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=esk3_0), inference(spm,[status(thm)],[c_0_32, c_0_58])).
% 0.14/0.39  cnf(c_0_68, negated_conjecture, (r1_tarski(esk4_0,k3_subset_1(esk2_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])])).
% 0.14/0.39  cnf(c_0_69, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.14/0.39  cnf(c_0_70, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_63, c_0_37])).
% 0.14/0.39  cnf(c_0_71, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.14/0.39  fof(c_0_72, plain, ![X9]:k3_xboole_0(X9,X9)=X9, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.14/0.39  cnf(c_0_73, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.14/0.39  cnf(c_0_74, negated_conjecture, (k3_xboole_0(esk3_0,k3_xboole_0(esk4_0,X1))=k3_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.14/0.39  cnf(c_0_75, negated_conjecture, (k3_xboole_0(esk4_0,k3_subset_1(esk2_0,esk5_0))=esk4_0), inference(spm,[status(thm)],[c_0_32, c_0_68])).
% 0.14/0.39  cnf(c_0_76, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=esk3_0), inference(rw,[status(thm)],[c_0_67, c_0_39])).
% 0.14/0.39  cnf(c_0_77, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_37]), c_0_37])).
% 0.14/0.39  cnf(c_0_78, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 0.14/0.39  cnf(c_0_79, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.14/0.39  cnf(c_0_80, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_73, c_0_37])).
% 0.14/0.39  cnf(c_0_81, negated_conjecture, (k3_xboole_0(esk3_0,k3_subset_1(esk2_0,esk5_0))=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_39]), c_0_76])).
% 0.14/0.39  cnf(c_0_82, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_71]), c_0_78]), c_0_79])).
% 0.14/0.39  cnf(c_0_83, negated_conjecture, (~r1_tarski(esk3_0,k3_subset_1(esk2_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  cnf(c_0_84, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])]), c_0_83]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 85
% 0.14/0.39  # Proof object clause steps            : 48
% 0.14/0.39  # Proof object formula steps           : 37
% 0.14/0.39  # Proof object conjectures             : 25
% 0.14/0.39  # Proof object clause conjectures      : 22
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 22
% 0.14/0.39  # Proof object initial formulas used   : 18
% 0.14/0.39  # Proof object generating inferences   : 17
% 0.14/0.39  # Proof object simplifying inferences  : 23
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 18
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 30
% 0.14/0.39  # Removed in clause preprocessing      : 1
% 0.14/0.39  # Initial clauses in saturation        : 29
% 0.14/0.39  # Processed clauses                    : 157
% 0.14/0.39  # ...of these trivial                  : 4
% 0.14/0.39  # ...subsumed                          : 12
% 0.14/0.39  # ...remaining for further processing  : 141
% 0.14/0.39  # Other redundant clauses eliminated   : 3
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 17
% 0.14/0.39  # Generated clauses                    : 238
% 0.14/0.39  # ...of the previous two non-trivial   : 176
% 0.14/0.39  # Contextual simplify-reflections      : 0
% 0.14/0.39  # Paramodulations                      : 235
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 3
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 93
% 0.14/0.39  #    Positive orientable unit clauses  : 45
% 0.14/0.39  #    Positive unorientable unit clauses: 2
% 0.14/0.39  #    Negative unit clauses             : 3
% 0.14/0.39  #    Non-unit-clauses                  : 43
% 0.14/0.39  # Current number of unprocessed clauses: 67
% 0.14/0.39  # ...number of literals in the above   : 99
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 47
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 1239
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 1149
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 7
% 0.14/0.39  # Unit Clause-clause subsumption calls : 349
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 51
% 0.14/0.39  # BW rewrite match successes           : 42
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 3953
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.034 s
% 0.14/0.39  # System time              : 0.004 s
% 0.14/0.39  # Total time               : 0.039 s
% 0.14/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
