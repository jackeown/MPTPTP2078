%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:44 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 132 expanded)
%              Number of clauses        :   32 (  46 expanded)
%              Number of leaves         :   10 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  188 ( 625 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t184_funct_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
                 => r1_tarski(k5_setfam_1(X1,X4),k5_setfam_1(X1,k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_funct_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(d12_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_setfam_1(X2,X1)
    <=> r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(t182_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
                 => ! [X5] :
                      ( m1_subset_1(X5,k1_zfmisc_1(X1))
                     => ( m1_setfam_1(X4,X5)
                       => m1_setfam_1(k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)),X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_funct_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k6_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2))) )
     => m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_funct_2)).

fof(dt_k7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
     => m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_funct_2)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
                   => r1_tarski(k5_setfam_1(X1,X4),k5_setfam_1(X1,k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t184_funct_2])).

fof(c_0_11,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | m1_subset_1(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_12,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & ~ v1_xboole_0(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & ~ r1_tarski(k5_setfam_1(esk2_0,esk5_0),k5_setfam_1(esk2_0,k6_funct_2(esk2_0,esk3_0,esk4_0,k7_funct_2(esk2_0,esk3_0,esk4_0,esk5_0)))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X8,X9] :
      ( ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(k3_tarski(X8),X9) )
      & ( ~ r1_tarski(esk1_2(X8,X9),X9)
        | r1_tarski(k3_tarski(X8),X9) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

fof(c_0_14,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13)))
      | k5_setfam_1(X13,X14) = k3_tarski(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

fof(c_0_18,plain,(
    ! [X11,X12] :
      ( ( ~ m1_setfam_1(X12,X11)
        | r1_tarski(X11,k3_tarski(X12)) )
      & ( ~ r1_tarski(X11,k3_tarski(X12))
        | m1_setfam_1(X12,X11) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).

fof(c_0_19,plain,(
    ! [X28,X29,X30,X31,X32] :
      ( v1_xboole_0(X28)
      | v1_xboole_0(X29)
      | ~ v1_funct_1(X30)
      | ~ v1_funct_2(X30,X28,X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(X28)))
      | ~ m1_subset_1(X32,k1_zfmisc_1(X28))
      | ~ m1_setfam_1(X31,X32)
      | m1_setfam_1(k6_funct_2(X28,X29,X30,k7_funct_2(X28,X29,X30,X31)),X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t182_funct_2])])])])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( ~ r1_tarski(k5_setfam_1(esk2_0,esk5_0),k5_setfam_1(esk2_0,k6_funct_2(esk2_0,esk3_0,esk4_0,k7_funct_2(esk2_0,esk3_0,esk4_0,esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r1_tarski(X2,k3_tarski(X1))
    | ~ m1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_setfam_1(k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)),X5)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
    | ~ m1_setfam_1(X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,X1),k1_zfmisc_1(esk2_0))
    | r1_tarski(k3_tarski(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_30,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(esk5_0),k5_setfam_1(esk2_0,k6_funct_2(esk2_0,esk3_0,esk4_0,k7_funct_2(esk2_0,esk3_0,esk4_0,esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_16])])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_tarski(X3,k3_tarski(k6_funct_2(X1,X2,X4,k7_funct_2(X1,X2,X4,X5))))
    | ~ v1_funct_2(X4,X1,X2)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_setfam_1(X5,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( m1_setfam_1(X2,X1)
    | ~ r1_tarski(X1,k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k3_tarski(esk5_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( ~ m1_subset_1(k6_funct_2(esk2_0,esk3_0,esk4_0,k7_funct_2(esk2_0,esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ r1_tarski(k3_tarski(esk5_0),k3_tarski(k6_funct_2(esk2_0,esk3_0,esk4_0,k7_funct_2(esk2_0,esk3_0,esk4_0,esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_25])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_tarski(X3,k3_tarski(k6_funct_2(X2,X1,X4,k7_funct_2(X2,X1,X4,X5))))
    | ~ v1_funct_2(X4,X2,X1)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X3,k3_tarski(X5)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k3_tarski(esk5_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_46,plain,(
    ! [X20,X21,X22,X23] :
      ( v1_xboole_0(X20)
      | v1_xboole_0(X21)
      | ~ v1_funct_1(X22)
      | ~ v1_funct_2(X22,X20,X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X21)))
      | m1_subset_1(k6_funct_2(X20,X21,X22,X23),k1_zfmisc_1(k1_zfmisc_1(X20))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_funct_2])])])).

cnf(c_0_47,negated_conjecture,
    ( ~ m1_subset_1(k6_funct_2(esk2_0,esk3_0,esk4_0,k7_funct_2(esk2_0,esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_16]),c_0_42]),c_0_43])]),c_0_44]),c_0_45])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_49,plain,(
    ! [X24,X25,X26,X27] :
      ( v1_xboole_0(X24)
      | v1_xboole_0(X25)
      | ~ v1_funct_1(X26)
      | ~ v1_funct_2(X26,X24,X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X24)))
      | m1_subset_1(k7_funct_2(X24,X25,X26,X27),k1_zfmisc_1(k1_zfmisc_1(X25))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_funct_2])])])).

cnf(c_0_50,negated_conjecture,
    ( ~ m1_subset_1(k7_funct_2(esk2_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_39]),c_0_40]),c_0_41])]),c_0_44]),c_0_45])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_39]),c_0_40]),c_0_41]),c_0_16])]),c_0_44]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:09:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.19/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t184_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))=>r1_tarski(k5_setfam_1(X1,X4),k5_setfam_1(X1,k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t184_funct_2)).
% 0.19/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.38  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.19/0.38  fof(d12_setfam_1, axiom, ![X1, X2]:(m1_setfam_1(X2,X1)<=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 0.19/0.38  fof(t182_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X1))=>(m1_setfam_1(X4,X5)=>m1_setfam_1(k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)),X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_funct_2)).
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(dt_k6_funct_2, axiom, ![X1, X2, X3, X4]:((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2))))=>m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_funct_2)).
% 0.19/0.38  fof(dt_k7_funct_2, axiom, ![X1, X2, X3, X4]:((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))))=>m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_funct_2)).
% 0.19/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))=>r1_tarski(k5_setfam_1(X1,X4),k5_setfam_1(X1,k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4))))))))), inference(assume_negation,[status(cth)],[t184_funct_2])).
% 0.19/0.38  fof(c_0_11, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|m1_subset_1(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.38  fof(c_0_12, negated_conjecture, (~v1_xboole_0(esk2_0)&(~v1_xboole_0(esk3_0)&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&~r1_tarski(k5_setfam_1(esk2_0,esk5_0),k5_setfam_1(esk2_0,k6_funct_2(esk2_0,esk3_0,esk4_0,k7_funct_2(esk2_0,esk3_0,esk4_0,esk5_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.19/0.38  fof(c_0_13, plain, ![X8, X9]:((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(k3_tarski(X8),X9))&(~r1_tarski(esk1_2(X8,X9),X9)|r1_tarski(k3_tarski(X8),X9))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.19/0.38  fof(c_0_14, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  cnf(c_0_15, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  fof(c_0_17, plain, ![X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13)))|k5_setfam_1(X13,X14)=k3_tarski(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.19/0.38  fof(c_0_18, plain, ![X11, X12]:((~m1_setfam_1(X12,X11)|r1_tarski(X11,k3_tarski(X12)))&(~r1_tarski(X11,k3_tarski(X12))|m1_setfam_1(X12,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).
% 0.19/0.38  fof(c_0_19, plain, ![X28, X29, X30, X31, X32]:(v1_xboole_0(X28)|(v1_xboole_0(X29)|(~v1_funct_1(X30)|~v1_funct_2(X30,X28,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|(~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(X28)))|(~m1_subset_1(X32,k1_zfmisc_1(X28))|(~m1_setfam_1(X31,X32)|m1_setfam_1(k6_funct_2(X28,X29,X30,k7_funct_2(X28,X29,X30,X31)),X32))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t182_funct_2])])])])).
% 0.19/0.38  cnf(c_0_20, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.38  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (~r1_tarski(k5_setfam_1(esk2_0,esk5_0),k5_setfam_1(esk2_0,k6_funct_2(esk2_0,esk3_0,esk4_0,k7_funct_2(esk2_0,esk3_0,esk4_0,esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_25, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_26, plain, (r1_tarski(X2,k3_tarski(X1))|~m1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_27, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_setfam_1(k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)),X5)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X5,k1_zfmisc_1(X1))|~m1_setfam_1(X4,X5)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_28, plain, (r1_tarski(k3_tarski(X1),X2)|~m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk1_2(esk5_0,X1),k1_zfmisc_1(esk2_0))|r1_tarski(k3_tarski(esk5_0),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.38  fof(c_0_30, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (~r1_tarski(k3_tarski(esk5_0),k5_setfam_1(esk2_0,k6_funct_2(esk2_0,esk3_0,esk4_0,k7_funct_2(esk2_0,esk3_0,esk4_0,esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_16])])).
% 0.19/0.38  cnf(c_0_32, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r1_tarski(X3,k3_tarski(k6_funct_2(X1,X2,X4,k7_funct_2(X1,X2,X4,X5))))|~v1_funct_2(X4,X1,X2)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_setfam_1(X5,X3)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.38  cnf(c_0_33, plain, (m1_setfam_1(X2,X1)|~r1_tarski(X1,k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (r1_tarski(k3_tarski(esk5_0),esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.38  cnf(c_0_36, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (~m1_subset_1(k6_funct_2(esk2_0,esk3_0,esk4_0,k7_funct_2(esk2_0,esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))|~r1_tarski(k3_tarski(esk5_0),k3_tarski(k6_funct_2(esk2_0,esk3_0,esk4_0,k7_funct_2(esk2_0,esk3_0,esk4_0,esk5_0))))), inference(spm,[status(thm)],[c_0_31, c_0_25])).
% 0.19/0.38  cnf(c_0_38, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r1_tarski(X3,k3_tarski(k6_funct_2(X2,X1,X4,k7_funct_2(X2,X1,X4,X5))))|~v1_funct_2(X4,X2,X1)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X3,k3_tarski(X5))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (m1_subset_1(k3_tarski(esk5_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.38  cnf(c_0_43, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_36])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  fof(c_0_46, plain, ![X20, X21, X22, X23]:(v1_xboole_0(X20)|v1_xboole_0(X21)|~v1_funct_1(X22)|~v1_funct_2(X22,X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X21)))|m1_subset_1(k6_funct_2(X20,X21,X22,X23),k1_zfmisc_1(k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_funct_2])])])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (~m1_subset_1(k6_funct_2(esk2_0,esk3_0,esk4_0,k7_funct_2(esk2_0,esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_16]), c_0_42]), c_0_43])]), c_0_44]), c_0_45])).
% 0.19/0.38  cnf(c_0_48, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.38  fof(c_0_49, plain, ![X24, X25, X26, X27]:(v1_xboole_0(X24)|v1_xboole_0(X25)|~v1_funct_1(X26)|~v1_funct_2(X26,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X24)))|m1_subset_1(k7_funct_2(X24,X25,X26,X27),k1_zfmisc_1(k1_zfmisc_1(X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_funct_2])])])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (~m1_subset_1(k7_funct_2(esk2_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_39]), c_0_40]), c_0_41])]), c_0_44]), c_0_45])).
% 0.19/0.38  cnf(c_0_51, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_39]), c_0_40]), c_0_41]), c_0_16])]), c_0_44]), c_0_45]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 53
% 0.19/0.38  # Proof object clause steps            : 32
% 0.19/0.38  # Proof object formula steps           : 21
% 0.19/0.38  # Proof object conjectures             : 19
% 0.19/0.38  # Proof object clause conjectures      : 16
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 19
% 0.19/0.38  # Proof object initial formulas used   : 10
% 0.19/0.38  # Proof object generating inferences   : 12
% 0.19/0.38  # Proof object simplifying inferences  : 25
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 10
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 21
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 21
% 0.19/0.38  # Processed clauses                    : 185
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 29
% 0.19/0.38  # ...remaining for further processing  : 156
% 0.19/0.38  # Other redundant clauses eliminated   : 2
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 177
% 0.19/0.38  # ...of the previous two non-trivial   : 173
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 175
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 2
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 134
% 0.19/0.38  #    Positive orientable unit clauses  : 20
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 8
% 0.19/0.38  #    Non-unit-clauses                  : 106
% 0.19/0.38  # Current number of unprocessed clauses: 29
% 0.19/0.38  # ...number of literals in the above   : 190
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 20
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 2507
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 1146
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 28
% 0.19/0.38  # Unit Clause-clause subsumption calls : 37
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 72
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 8191
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.044 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.048 s
% 0.19/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
