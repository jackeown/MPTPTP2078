%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:51 EST 2020

% Result     : Theorem 1.38s
% Output     : CNFRefutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 122 expanded)
%              Number of clauses        :   43 (  53 expanded)
%              Number of leaves         :   14 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  192 ( 371 expanded)
%              Number of equality atoms :   45 (  78 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(t59_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( r1_tarski(X2,X3)
           => r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

fof(t8_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(k1_setfam_1(X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(dt_k8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(c_0_14,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | ~ r2_hidden(X19,X18)
      | r2_hidden(X19,X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_15,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X27,k1_zfmisc_1(X28))
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | m1_subset_1(X27,k1_zfmisc_1(X28)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_16,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,plain,(
    ! [X32,X33] :
      ( ( r2_hidden(esk2_2(X32,X33),X32)
        | X32 = k1_xboole_0
        | r1_tarski(X33,k1_setfam_1(X32)) )
      & ( ~ r1_tarski(X33,esk2_2(X32,X33))
        | X32 = k1_xboole_0
        | r1_tarski(X33,k1_setfam_1(X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
           => ( r1_tarski(X2,X3)
             => r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_setfam_1])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & r1_tarski(esk4_0,esk5_0)
    & ~ r1_tarski(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_23,plain,(
    ! [X35,X36,X37] :
      ( ~ r2_hidden(X35,X36)
      | ~ r1_tarski(X35,X37)
      | r1_tarski(k1_setfam_1(X36),X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_2(X1,X2),X3)
    | r1_tarski(X2,k1_setfam_1(X1))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_27,plain,
    ( r1_tarski(k1_setfam_1(X2),X3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk2_2(esk4_0,X1),esk5_0)
    | r1_tarski(X1,k1_setfam_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_30,plain,(
    ! [X21,X22] :
      ( ( X22 = k1_xboole_0
        | k8_setfam_1(X21,X22) = k6_setfam_1(X21,X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21))) )
      & ( X22 != k1_xboole_0
        | k8_setfam_1(X21,X22) = X21
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

fof(c_0_31,plain,(
    ! [X29,X30,X31] :
      ( ~ r2_hidden(X29,X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(X31))
      | m1_subset_1(X29,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_32,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X15,X14)
        | r2_hidden(X15,X14)
        | v1_xboole_0(X14) )
      & ( ~ r2_hidden(X15,X14)
        | m1_subset_1(X15,X14)
        | v1_xboole_0(X14) )
      & ( ~ m1_subset_1(X15,X14)
        | v1_xboole_0(X15)
        | ~ v1_xboole_0(X14) )
      & ( ~ v1_xboole_0(X15)
        | m1_subset_1(X15,X14)
        | ~ v1_xboole_0(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_33,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X23)))
      | m1_subset_1(k8_setfam_1(X23,X24),k1_zfmisc_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).

fof(c_0_34,plain,(
    ! [X16] : ~ v1_xboole_0(k1_zfmisc_1(X16)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_35,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(esk4_0))
    | r1_tarski(k1_setfam_1(esk5_0),X2)
    | ~ r1_tarski(esk2_2(esk4_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_29])).

fof(c_0_37,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25)))
      | k6_setfam_1(X25,X26) = k1_setfam_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk2_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k1_setfam_1(esk5_0),esk2_2(esk4_0,X1))
    | r1_tarski(X1,k1_setfam_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( k6_setfam_1(esk3_0,esk4_0) = k8_setfam_1(esk3_0,esk4_0)
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_17])).

cnf(c_0_50,plain,
    ( r2_hidden(k8_setfam_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k1_setfam_1(esk5_0),k1_setfam_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( k1_setfam_1(esk4_0) = k8_setfam_1(esk3_0,esk4_0)
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_39])])).

cnf(c_0_53,negated_conjecture,
    ( k6_setfam_1(esk3_0,esk5_0) = k8_setfam_1(esk3_0,esk5_0)
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_48])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_55,plain,
    ( m1_subset_1(k8_setfam_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(k1_zfmisc_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_57,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k1_setfam_1(esk5_0),k8_setfam_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( k1_setfam_1(esk5_0) = k8_setfam_1(esk3_0,esk5_0)
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_53]),c_0_48])])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_60,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_61,plain,(
    ! [X20] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X20)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_62,plain,
    ( r1_tarski(k8_setfam_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( esk5_0 = esk4_0
    | ~ r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_25])).

cnf(c_0_64,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_67,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(k8_setfam_1(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_62]),c_0_48])])).

cnf(c_0_69,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])])).

cnf(c_0_70,plain,
    ( k8_setfam_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_66]),c_0_67])])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.38/1.56  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.38/1.56  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.38/1.56  #
% 1.38/1.56  # Preprocessing time       : 0.016 s
% 1.38/1.56  # Presaturation interreduction done
% 1.38/1.56  
% 1.38/1.56  # Proof found!
% 1.38/1.56  # SZS status Theorem
% 1.38/1.56  # SZS output start CNFRefutation
% 1.38/1.56  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 1.38/1.56  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.38/1.56  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 1.38/1.56  fof(t59_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 1.38/1.56  fof(t8_setfam_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(k1_setfam_1(X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_setfam_1)).
% 1.38/1.56  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.38/1.56  fof(d10_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((X2!=k1_xboole_0=>k8_setfam_1(X1,X2)=k6_setfam_1(X1,X2))&(X2=k1_xboole_0=>k8_setfam_1(X1,X2)=X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 1.38/1.56  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 1.38/1.56  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.38/1.56  fof(dt_k8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 1.38/1.56  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.38/1.56  fof(redefinition_k6_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k6_setfam_1(X1,X2)=k1_setfam_1(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 1.38/1.56  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.38/1.56  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.38/1.56  fof(c_0_14, plain, ![X17, X18, X19]:(~m1_subset_1(X18,k1_zfmisc_1(X17))|(~r2_hidden(X19,X18)|r2_hidden(X19,X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 1.38/1.56  fof(c_0_15, plain, ![X27, X28]:((~m1_subset_1(X27,k1_zfmisc_1(X28))|r1_tarski(X27,X28))&(~r1_tarski(X27,X28)|m1_subset_1(X27,k1_zfmisc_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.38/1.56  cnf(c_0_16, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.38/1.56  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.38/1.56  fof(c_0_18, plain, ![X32, X33]:((r2_hidden(esk2_2(X32,X33),X32)|(X32=k1_xboole_0|r1_tarski(X33,k1_setfam_1(X32))))&(~r1_tarski(X33,esk2_2(X32,X33))|(X32=k1_xboole_0|r1_tarski(X33,k1_setfam_1(X32))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 1.38/1.56  fof(c_0_19, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t59_setfam_1])).
% 1.38/1.56  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 1.38/1.56  cnf(c_0_21, plain, (r2_hidden(esk2_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.38/1.56  fof(c_0_22, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))&(r1_tarski(esk4_0,esk5_0)&~r1_tarski(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 1.38/1.56  fof(c_0_23, plain, ![X35, X36, X37]:(~r2_hidden(X35,X36)|~r1_tarski(X35,X37)|r1_tarski(k1_setfam_1(X36),X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).
% 1.38/1.56  cnf(c_0_24, plain, (X1=k1_xboole_0|r2_hidden(esk2_2(X1,X2),X3)|r1_tarski(X2,k1_setfam_1(X1))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 1.38/1.56  cnf(c_0_25, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.38/1.56  fof(c_0_26, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.38/1.56  cnf(c_0_27, plain, (r1_tarski(k1_setfam_1(X2),X3)|~r2_hidden(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.38/1.56  cnf(c_0_28, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk2_2(esk4_0,X1),esk5_0)|r1_tarski(X1,k1_setfam_1(esk4_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 1.38/1.56  cnf(c_0_29, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.38/1.56  fof(c_0_30, plain, ![X21, X22]:((X22=k1_xboole_0|k8_setfam_1(X21,X22)=k6_setfam_1(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21))))&(X22!=k1_xboole_0|k8_setfam_1(X21,X22)=X21|~m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).
% 1.38/1.56  fof(c_0_31, plain, ![X29, X30, X31]:(~r2_hidden(X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(X31))|m1_subset_1(X29,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 1.38/1.56  fof(c_0_32, plain, ![X14, X15]:(((~m1_subset_1(X15,X14)|r2_hidden(X15,X14)|v1_xboole_0(X14))&(~r2_hidden(X15,X14)|m1_subset_1(X15,X14)|v1_xboole_0(X14)))&((~m1_subset_1(X15,X14)|v1_xboole_0(X15)|~v1_xboole_0(X14))&(~v1_xboole_0(X15)|m1_subset_1(X15,X14)|~v1_xboole_0(X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 1.38/1.56  fof(c_0_33, plain, ![X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X23)))|m1_subset_1(k8_setfam_1(X23,X24),k1_zfmisc_1(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).
% 1.38/1.56  fof(c_0_34, plain, ![X16]:~v1_xboole_0(k1_zfmisc_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 1.38/1.56  cnf(c_0_35, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(X1,k1_setfam_1(esk4_0))|r1_tarski(k1_setfam_1(esk5_0),X2)|~r1_tarski(esk2_2(esk4_0,X1),X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.38/1.56  cnf(c_0_36, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_29])).
% 1.38/1.56  fof(c_0_37, plain, ![X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25)))|k6_setfam_1(X25,X26)=k1_setfam_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).
% 1.38/1.56  cnf(c_0_38, plain, (X1=k1_xboole_0|k8_setfam_1(X2,X1)=k6_setfam_1(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.38/1.56  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.38/1.56  cnf(c_0_40, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.38/1.56  cnf(c_0_41, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.38/1.56  cnf(c_0_42, plain, (m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.38/1.56  cnf(c_0_43, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.38/1.56  cnf(c_0_44, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk2_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.38/1.56  cnf(c_0_45, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k1_setfam_1(esk5_0),esk2_2(esk4_0,X1))|r1_tarski(X1,k1_setfam_1(esk4_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.38/1.56  cnf(c_0_46, plain, (k6_setfam_1(X2,X1)=k1_setfam_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.38/1.56  cnf(c_0_47, negated_conjecture, (k6_setfam_1(esk3_0,esk4_0)=k8_setfam_1(esk3_0,esk4_0)|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.38/1.56  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.38/1.56  cnf(c_0_49, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_40, c_0_17])).
% 1.38/1.56  cnf(c_0_50, plain, (r2_hidden(k8_setfam_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 1.38/1.56  cnf(c_0_51, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k1_setfam_1(esk5_0),k1_setfam_1(esk4_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 1.38/1.56  cnf(c_0_52, negated_conjecture, (k1_setfam_1(esk4_0)=k8_setfam_1(esk3_0,esk4_0)|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_39])])).
% 1.38/1.56  cnf(c_0_53, negated_conjecture, (k6_setfam_1(esk3_0,esk5_0)=k8_setfam_1(esk3_0,esk5_0)|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_48])).
% 1.38/1.56  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.38/1.56  cnf(c_0_55, plain, (m1_subset_1(k8_setfam_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r1_tarski(k1_zfmisc_1(X1),X3)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 1.38/1.56  cnf(c_0_56, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.38/1.56  cnf(c_0_57, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k1_setfam_1(esk5_0),k8_setfam_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 1.38/1.56  cnf(c_0_58, negated_conjecture, (k1_setfam_1(esk5_0)=k8_setfam_1(esk3_0,esk5_0)|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_53]), c_0_48])])).
% 1.38/1.56  cnf(c_0_59, negated_conjecture, (~r1_tarski(k8_setfam_1(esk3_0,esk5_0),k8_setfam_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.38/1.56  fof(c_0_60, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 1.38/1.56  fof(c_0_61, plain, ![X20]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X20)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 1.38/1.56  cnf(c_0_62, plain, (r1_tarski(k8_setfam_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 1.38/1.56  cnf(c_0_63, negated_conjecture, (esk5_0=esk4_0|~r1_tarski(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_25])).
% 1.38/1.56  cnf(c_0_64, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 1.38/1.56  cnf(c_0_65, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 1.38/1.56  cnf(c_0_66, plain, (k8_setfam_1(X2,X1)=X2|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.38/1.56  cnf(c_0_67, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.38/1.56  cnf(c_0_68, negated_conjecture, (~r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(k8_setfam_1(esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_62]), c_0_48])])).
% 1.38/1.56  cnf(c_0_69, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])])).
% 1.38/1.56  cnf(c_0_70, plain, (k8_setfam_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_66]), c_0_67])])).
% 1.38/1.56  cnf(c_0_71, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_36])]), ['proof']).
% 1.38/1.56  # SZS output end CNFRefutation
% 1.38/1.56  # Proof object total steps             : 72
% 1.38/1.56  # Proof object clause steps            : 43
% 1.38/1.56  # Proof object formula steps           : 29
% 1.38/1.56  # Proof object conjectures             : 21
% 1.38/1.56  # Proof object clause conjectures      : 18
% 1.38/1.56  # Proof object formula conjectures     : 3
% 1.38/1.56  # Proof object initial clauses used    : 21
% 1.38/1.56  # Proof object initial formulas used   : 14
% 1.38/1.56  # Proof object generating inferences   : 19
% 1.38/1.56  # Proof object simplifying inferences  : 18
% 1.38/1.56  # Training examples: 0 positive, 0 negative
% 1.38/1.56  # Parsed axioms                        : 15
% 1.38/1.56  # Removed by relevancy pruning/SinE    : 0
% 1.38/1.56  # Initial clauses                      : 29
% 1.38/1.56  # Removed in clause preprocessing      : 0
% 1.38/1.56  # Initial clauses in saturation        : 29
% 1.38/1.56  # Processed clauses                    : 14825
% 1.38/1.56  # ...of these trivial                  : 4
% 1.38/1.56  # ...subsumed                          : 11770
% 1.38/1.56  # ...remaining for further processing  : 3051
% 1.38/1.56  # Other redundant clauses eliminated   : 5
% 1.38/1.56  # Clauses deleted for lack of memory   : 0
% 1.38/1.56  # Backward-subsumed                    : 248
% 1.38/1.56  # Backward-rewritten                   : 1579
% 1.38/1.56  # Generated clauses                    : 65301
% 1.38/1.56  # ...of the previous two non-trivial   : 62452
% 1.38/1.56  # Contextual simplify-reflections      : 13
% 1.38/1.56  # Paramodulations                      : 65278
% 1.38/1.56  # Factorizations                       : 18
% 1.38/1.56  # Equation resolutions                 : 5
% 1.38/1.56  # Propositional unsat checks           : 0
% 1.38/1.56  #    Propositional check models        : 0
% 1.38/1.56  #    Propositional check unsatisfiable : 0
% 1.38/1.56  #    Propositional clauses             : 0
% 1.38/1.56  #    Propositional clauses after purity: 0
% 1.38/1.56  #    Propositional unsat core size     : 0
% 1.38/1.56  #    Propositional preprocessing time  : 0.000
% 1.38/1.56  #    Propositional encoding time       : 0.000
% 1.38/1.56  #    Propositional solver time         : 0.000
% 1.38/1.56  #    Success case prop preproc time    : 0.000
% 1.38/1.56  #    Success case prop encoding time   : 0.000
% 1.38/1.56  #    Success case prop solver time     : 0.000
% 1.38/1.56  # Current number of processed clauses  : 1191
% 1.38/1.56  #    Positive orientable unit clauses  : 19
% 1.38/1.56  #    Positive unorientable unit clauses: 0
% 1.38/1.56  #    Negative unit clauses             : 3
% 1.38/1.56  #    Non-unit-clauses                  : 1169
% 1.38/1.56  # Current number of unprocessed clauses: 44684
% 1.38/1.56  # ...number of literals in the above   : 270900
% 1.38/1.56  # Current number of archived formulas  : 0
% 1.38/1.56  # Current number of archived clauses   : 1855
% 1.38/1.56  # Clause-clause subsumption calls (NU) : 1583604
% 1.38/1.56  # Rec. Clause-clause subsumption calls : 410517
% 1.38/1.56  # Non-unit clause-clause subsumptions  : 9486
% 1.38/1.56  # Unit Clause-clause subsumption calls : 2349
% 1.38/1.56  # Rewrite failures with RHS unbound    : 0
% 1.38/1.56  # BW rewrite match attempts            : 17
% 1.38/1.56  # BW rewrite match successes           : 4
% 1.38/1.56  # Condensation attempts                : 0
% 1.38/1.56  # Condensation successes               : 0
% 1.38/1.56  # Termbank termtop insertions          : 1464483
% 1.38/1.57  
% 1.38/1.57  # -------------------------------------------------
% 1.38/1.57  # User time                : 1.199 s
% 1.38/1.57  # System time              : 0.026 s
% 1.38/1.57  # Total time               : 1.225 s
% 1.38/1.57  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
