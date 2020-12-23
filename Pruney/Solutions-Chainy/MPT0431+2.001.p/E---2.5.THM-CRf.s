%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:05 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 210 expanded)
%              Number of clauses        :   50 ( 103 expanded)
%              Number of leaves         :    7 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  183 (1223 expanded)
%              Number of equality atoms :   33 ( 279 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_setfam_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( v3_setfam_1(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) )
         => ! [X3] :
              ( ( v3_setfam_1(X3,X1)
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
             => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X1),X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_setfam_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(d13_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v3_setfam_1(X2,X1)
      <=> ~ r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ( v3_setfam_1(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) )
           => ! [X3] :
                ( ( v3_setfam_1(X3,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X1),X2,X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t63_setfam_1])).

fof(c_0_8,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X14,X13)
        | r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X18)
        | r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k2_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_9,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | ~ r2_hidden(X22,X21)
      | r2_hidden(X22,X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & v3_setfam_1(esk4_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & v3_setfam_1(esk5_0,esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(esk3_0),esk4_0,esk5_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X1)
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_15])).

cnf(c_0_19,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( k2_xboole_0(esk4_0,X1) = X1
    | r2_hidden(esk2_3(esk4_0,X1,X1),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
    | ~ r2_hidden(esk2_3(X3,X4,k2_xboole_0(X1,X2)),X3)
    | ~ r2_hidden(esk2_3(X3,X4,k2_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X1) = X1
    | r2_hidden(esk2_3(X1,X1,X1),X1) ),
    inference(ef,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( k2_xboole_0(esk4_0,k1_zfmisc_1(esk3_0)) = k1_zfmisc_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_21]),c_0_18])).

fof(c_0_27,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_22])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,X3)
    | ~ r2_hidden(esk2_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_18])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_24]),c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( k2_xboole_0(esk5_0,X1) = X1
    | r2_hidden(esk2_3(esk5_0,X1,X1),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_18])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( k2_xboole_0(esk4_0,X1) = X1
    | r2_hidden(esk2_3(esk4_0,X1,X1),X2)
    | X2 != k1_zfmisc_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_18])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( k2_xboole_0(esk5_0,k1_zfmisc_1(esk3_0)) = k1_zfmisc_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_34]),c_0_18])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_42,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | ~ m1_subset_1(X25,k1_zfmisc_1(X23))
      | k4_subset_1(X23,X24,X25) = k2_xboole_0(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_43,negated_conjecture,
    ( k2_xboole_0(esk4_0,X1) = X1
    | X1 != k1_zfmisc_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(X1,k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(esk1_2(X1,k1_zfmisc_1(esk3_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X2)
    | r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(esk3_0),esk4_0,esk5_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_47,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_48,plain,(
    ! [X26,X27] :
      ( ( ~ v3_setfam_1(X27,X26)
        | ~ r2_hidden(X26,X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))) )
      & ( r2_hidden(X26,X27)
        | v3_setfam_1(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_setfam_1])])])])).

fof(c_0_49,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(X1,X2)
    | X2 != k1_zfmisc_1(esk3_0)
    | ~ r2_hidden(esk1_2(X1,X2),esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(X1,esk5_0),k1_zfmisc_1(esk3_0)),X1)
    | r1_tarski(k2_xboole_0(X1,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( ~ v3_setfam_1(k2_xboole_0(esk4_0,esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_22]),c_0_13])])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | v3_setfam_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk3_0,k2_xboole_0(esk4_0,esk5_0))
    | ~ m1_subset_1(k2_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,plain,
    ( ~ v3_setfam_1(X1,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( v3_setfam_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_60,negated_conjecture,
    ( v3_setfam_1(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk3_0,k2_xboole_0(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_13])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_60]),c_0_22])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_61]),c_0_62]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.67  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.47/0.67  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.47/0.67  #
% 0.47/0.67  # Preprocessing time       : 0.027 s
% 0.47/0.67  # Presaturation interreduction done
% 0.47/0.67  
% 0.47/0.67  # Proof found!
% 0.47/0.67  # SZS status Theorem
% 0.47/0.67  # SZS output start CNFRefutation
% 0.47/0.67  fof(t63_setfam_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((v3_setfam_1(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))))=>![X3]:((v3_setfam_1(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))))=>v3_setfam_1(k4_subset_1(k1_zfmisc_1(X1),X2,X3),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_setfam_1)).
% 0.47/0.67  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.47/0.67  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.47/0.67  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.47/0.67  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.47/0.67  fof(d13_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v3_setfam_1(X2,X1)<=>~(r2_hidden(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_setfam_1)).
% 0.47/0.67  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.47/0.67  fof(c_0_7, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:((v3_setfam_1(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))))=>![X3]:((v3_setfam_1(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))))=>v3_setfam_1(k4_subset_1(k1_zfmisc_1(X1),X2,X3),X1))))), inference(assume_negation,[status(cth)],[t63_setfam_1])).
% 0.47/0.67  fof(c_0_8, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(r2_hidden(X14,X11)|r2_hidden(X14,X12))|X13!=k2_xboole_0(X11,X12))&((~r2_hidden(X15,X11)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))&(~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))))&(((~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17)))&(r2_hidden(esk2_3(X16,X17,X18),X18)|(r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k2_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.47/0.67  fof(c_0_9, plain, ![X20, X21, X22]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|(~r2_hidden(X22,X21)|r2_hidden(X22,X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.47/0.67  fof(c_0_10, negated_conjecture, (~v1_xboole_0(esk3_0)&((v3_setfam_1(esk4_0,esk3_0)&m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))))&((v3_setfam_1(esk5_0,esk3_0)&m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))))&~v3_setfam_1(k4_subset_1(k1_zfmisc_1(esk3_0),esk4_0,esk5_0),esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.47/0.67  cnf(c_0_11, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.47/0.67  cnf(c_0_12, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.47/0.67  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.67  cnf(c_0_14, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.47/0.67  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X1)|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_11])).
% 0.47/0.67  cnf(c_0_16, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.47/0.67  cnf(c_0_17, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.47/0.67  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_15])).
% 0.47/0.67  cnf(c_0_19, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.47/0.67  cnf(c_0_20, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_16])).
% 0.47/0.67  cnf(c_0_21, negated_conjecture, (k2_xboole_0(esk4_0,X1)=X1|r2_hidden(esk2_3(esk4_0,X1,X1),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.47/0.67  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.67  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)|~r2_hidden(esk2_3(X3,X4,k2_xboole_0(X1,X2)),X3)|~r2_hidden(esk2_3(X3,X4,k2_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.47/0.67  cnf(c_0_24, plain, (k2_xboole_0(X1,X1)=X1|r2_hidden(esk2_3(X1,X1,X1),X1)), inference(ef,[status(thm)],[c_0_15])).
% 0.47/0.67  cnf(c_0_25, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.47/0.67  cnf(c_0_26, negated_conjecture, (k2_xboole_0(esk4_0,k1_zfmisc_1(esk3_0))=k1_zfmisc_1(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_21]), c_0_18])).
% 0.47/0.67  fof(c_0_27, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.47/0.67  cnf(c_0_28, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(esk3_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_12, c_0_22])).
% 0.47/0.67  cnf(c_0_29, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X2,X3)|~r2_hidden(esk2_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_23, c_0_18])).
% 0.47/0.67  cnf(c_0_30, plain, (k2_xboole_0(X1,X1)=X1), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_24]), c_0_24])).
% 0.47/0.67  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,X2)|X2!=k1_zfmisc_1(esk3_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.47/0.67  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.47/0.67  cnf(c_0_33, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_25])).
% 0.47/0.67  cnf(c_0_34, negated_conjecture, (k2_xboole_0(esk5_0,X1)=X1|r2_hidden(esk2_3(esk5_0,X1,X1),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_28, c_0_18])).
% 0.47/0.67  cnf(c_0_35, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.47/0.67  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=X2|~r2_hidden(esk2_3(X1,X2,X2),X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.47/0.67  cnf(c_0_37, negated_conjecture, (k2_xboole_0(esk4_0,X1)=X1|r2_hidden(esk2_3(esk4_0,X1,X1),X2)|X2!=k1_zfmisc_1(esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_18])).
% 0.47/0.67  cnf(c_0_38, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.47/0.67  cnf(c_0_39, negated_conjecture, (k2_xboole_0(esk5_0,k1_zfmisc_1(esk3_0))=k1_zfmisc_1(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_34]), c_0_18])).
% 0.47/0.67  cnf(c_0_40, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_35])).
% 0.47/0.67  cnf(c_0_41, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.47/0.67  fof(c_0_42, plain, ![X23, X24, X25]:(~m1_subset_1(X24,k1_zfmisc_1(X23))|~m1_subset_1(X25,k1_zfmisc_1(X23))|k4_subset_1(X23,X24,X25)=k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.47/0.67  cnf(c_0_43, negated_conjecture, (k2_xboole_0(esk4_0,X1)=X1|X1!=k1_zfmisc_1(esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.47/0.67  cnf(c_0_44, negated_conjecture, (r1_tarski(X1,k1_zfmisc_1(esk3_0))|~r2_hidden(esk1_2(X1,k1_zfmisc_1(esk3_0)),esk5_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.47/0.67  cnf(c_0_45, plain, (r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X2)|r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X1)|r1_tarski(k2_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.47/0.67  cnf(c_0_46, negated_conjecture, (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(esk3_0),esk4_0,esk5_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.67  cnf(c_0_47, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.47/0.67  fof(c_0_48, plain, ![X26, X27]:((~v3_setfam_1(X27,X26)|~r2_hidden(X26,X27)|~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))))&(r2_hidden(X26,X27)|v3_setfam_1(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_setfam_1])])])])).
% 0.47/0.67  fof(c_0_49, plain, ![X28, X29]:((~m1_subset_1(X28,k1_zfmisc_1(X29))|r1_tarski(X28,X29))&(~r1_tarski(X28,X29)|m1_subset_1(X28,k1_zfmisc_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.47/0.67  cnf(c_0_50, negated_conjecture, (r1_tarski(X1,X2)|X2!=k1_zfmisc_1(esk3_0)|~r2_hidden(esk1_2(X1,X2),esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_43])).
% 0.47/0.67  cnf(c_0_51, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(X1,esk5_0),k1_zfmisc_1(esk3_0)),X1)|r1_tarski(k2_xboole_0(X1,esk5_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.47/0.67  cnf(c_0_52, negated_conjecture, (~v3_setfam_1(k2_xboole_0(esk4_0,esk5_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_22]), c_0_13])])).
% 0.47/0.67  cnf(c_0_53, plain, (r2_hidden(X1,X2)|v3_setfam_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.47/0.67  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.47/0.67  cnf(c_0_55, negated_conjecture, (r1_tarski(k2_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.47/0.67  cnf(c_0_56, negated_conjecture, (r2_hidden(esk3_0,k2_xboole_0(esk4_0,esk5_0))|~m1_subset_1(k2_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.47/0.67  cnf(c_0_57, negated_conjecture, (m1_subset_1(k2_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.47/0.67  cnf(c_0_58, plain, (~v3_setfam_1(X1,X2)|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.47/0.67  cnf(c_0_59, negated_conjecture, (v3_setfam_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.67  cnf(c_0_60, negated_conjecture, (v3_setfam_1(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.67  cnf(c_0_61, negated_conjecture, (r2_hidden(esk3_0,k2_xboole_0(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 0.47/0.67  cnf(c_0_62, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_13])])).
% 0.47/0.67  cnf(c_0_63, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_60]), c_0_22])])).
% 0.47/0.67  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_61]), c_0_62]), c_0_63]), ['proof']).
% 0.47/0.67  # SZS output end CNFRefutation
% 0.47/0.67  # Proof object total steps             : 65
% 0.47/0.67  # Proof object clause steps            : 50
% 0.47/0.67  # Proof object formula steps           : 15
% 0.47/0.67  # Proof object conjectures             : 28
% 0.47/0.67  # Proof object clause conjectures      : 25
% 0.47/0.67  # Proof object formula conjectures     : 3
% 0.47/0.67  # Proof object initial clauses used    : 18
% 0.47/0.67  # Proof object initial formulas used   : 7
% 0.47/0.67  # Proof object generating inferences   : 31
% 0.47/0.67  # Proof object simplifying inferences  : 15
% 0.47/0.67  # Training examples: 0 positive, 0 negative
% 0.47/0.67  # Parsed axioms                        : 7
% 0.47/0.67  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.67  # Initial clauses                      : 21
% 0.47/0.67  # Removed in clause preprocessing      : 0
% 0.47/0.67  # Initial clauses in saturation        : 21
% 0.47/0.67  # Processed clauses                    : 3996
% 0.47/0.67  # ...of these trivial                  : 243
% 0.47/0.67  # ...subsumed                          : 3140
% 0.47/0.67  # ...remaining for further processing  : 613
% 0.47/0.67  # Other redundant clauses eliminated   : 45
% 0.47/0.67  # Clauses deleted for lack of memory   : 0
% 0.47/0.67  # Backward-subsumed                    : 6
% 0.47/0.67  # Backward-rewritten                   : 7
% 0.47/0.67  # Generated clauses                    : 29805
% 0.47/0.67  # ...of the previous two non-trivial   : 22885
% 0.47/0.67  # Contextual simplify-reflections      : 11
% 0.47/0.67  # Paramodulations                      : 29106
% 0.47/0.67  # Factorizations                       : 618
% 0.47/0.67  # Equation resolutions                 : 74
% 0.47/0.67  # Propositional unsat checks           : 0
% 0.47/0.67  #    Propositional check models        : 0
% 0.47/0.67  #    Propositional check unsatisfiable : 0
% 0.47/0.67  #    Propositional clauses             : 0
% 0.47/0.67  #    Propositional clauses after purity: 0
% 0.47/0.67  #    Propositional unsat core size     : 0
% 0.47/0.67  #    Propositional preprocessing time  : 0.000
% 0.47/0.67  #    Propositional encoding time       : 0.000
% 0.47/0.67  #    Propositional solver time         : 0.000
% 0.47/0.67  #    Success case prop preproc time    : 0.000
% 0.47/0.67  #    Success case prop encoding time   : 0.000
% 0.47/0.67  #    Success case prop solver time     : 0.000
% 0.47/0.67  # Current number of processed clauses  : 572
% 0.47/0.67  #    Positive orientable unit clauses  : 154
% 0.47/0.67  #    Positive unorientable unit clauses: 0
% 0.47/0.67  #    Negative unit clauses             : 9
% 0.47/0.67  #    Non-unit-clauses                  : 409
% 0.47/0.67  # Current number of unprocessed clauses: 18819
% 0.47/0.67  # ...number of literals in the above   : 77022
% 0.47/0.67  # Current number of archived formulas  : 0
% 0.47/0.67  # Current number of archived clauses   : 41
% 0.47/0.67  # Clause-clause subsumption calls (NU) : 49059
% 0.47/0.67  # Rec. Clause-clause subsumption calls : 23190
% 0.47/0.67  # Non-unit clause-clause subsumptions  : 2742
% 0.47/0.67  # Unit Clause-clause subsumption calls : 601
% 0.47/0.67  # Rewrite failures with RHS unbound    : 0
% 0.47/0.67  # BW rewrite match attempts            : 1034
% 0.47/0.67  # BW rewrite match successes           : 5
% 0.47/0.67  # Condensation attempts                : 0
% 0.47/0.67  # Condensation successes               : 0
% 0.47/0.67  # Termbank termtop insertions          : 475385
% 0.47/0.67  
% 0.47/0.67  # -------------------------------------------------
% 0.47/0.67  # User time                : 0.313 s
% 0.47/0.67  # System time              : 0.016 s
% 0.47/0.67  # Total time               : 0.329 s
% 0.47/0.67  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
