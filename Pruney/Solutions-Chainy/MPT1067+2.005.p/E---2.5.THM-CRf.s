%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:44 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 140 expanded)
%              Number of clauses        :   36 (  50 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  211 ( 668 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   12 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_funct_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(d12_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_setfam_1(X2,X1)
    <=> r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_funct_2)).

fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(dt_k6_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2))) )
     => m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_funct_2)).

fof(dt_k7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
     => m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_funct_2)).

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
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X26,k1_zfmisc_1(X27))
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | m1_subset_1(X26,k1_zfmisc_1(X27)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_13,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    & ~ v1_xboole_0(esk5_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0)))
    & ~ r1_tarski(k5_setfam_1(esk4_0,esk7_0),k5_setfam_1(esk4_0,k6_funct_2(esk4_0,esk5_0,esk6_0,k7_funct_2(esk4_0,esk5_0,esk6_0,esk7_0)))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_14,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))
      | k5_setfam_1(X24,X25) = k3_tarski(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

fof(c_0_15,plain,(
    ! [X22,X23] :
      ( ( ~ m1_setfam_1(X23,X22)
        | r1_tarski(X22,k3_tarski(X23)) )
      & ( ~ r1_tarski(X22,k3_tarski(X23))
        | m1_setfam_1(X23,X22) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).

fof(c_0_16,plain,(
    ! [X36,X37,X38,X39,X40] :
      ( v1_xboole_0(X36)
      | v1_xboole_0(X37)
      | ~ v1_funct_1(X38)
      | ~ v1_funct_2(X38,X36,X37)
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | ~ m1_subset_1(X39,k1_zfmisc_1(k1_zfmisc_1(X36)))
      | ~ m1_subset_1(X40,k1_zfmisc_1(X36))
      | ~ m1_setfam_1(X39,X40)
      | m1_setfam_1(k6_funct_2(X36,X37,X38,k7_funct_2(X36,X37,X38,X39)),X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t182_funct_2])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( ~ r1_tarski(k5_setfam_1(esk4_0,esk7_0),k5_setfam_1(esk4_0,k6_funct_2(esk4_0,esk5_0,esk6_0,k7_funct_2(esk4_0,esk5_0,esk6_0,esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r1_tarski(X2,k3_tarski(X1))
    | ~ m1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_setfam_1(k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)),X5)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
    | ~ m1_setfam_1(X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_25,plain,(
    ! [X19,X20] :
      ( ( r2_hidden(esk3_2(X19,X20),X19)
        | r1_tarski(k3_tarski(X19),X20) )
      & ( ~ r1_tarski(esk3_2(X19,X20),X20)
        | r1_tarski(k3_tarski(X19),X20) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(esk7_0),k5_setfam_1(esk4_0,k6_funct_2(esk4_0,esk5_0,esk6_0,k7_funct_2(esk4_0,esk5_0,esk6_0,esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_tarski(X3,k3_tarski(k6_funct_2(X1,X2,X4,k7_funct_2(X1,X2,X4,X5))))
    | ~ v1_funct_2(X4,X1,X2)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_setfam_1(X5,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( m1_setfam_1(X2,X1)
    | ~ r1_tarski(X1,k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_31,plain,(
    ! [X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X14,X13)
        | r1_tarski(X14,X12)
        | X13 != k1_zfmisc_1(X12) )
      & ( ~ r1_tarski(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k1_zfmisc_1(X12) )
      & ( ~ r2_hidden(esk2_2(X16,X17),X17)
        | ~ r1_tarski(esk2_2(X16,X17),X16)
        | X17 = k1_zfmisc_1(X16) )
      & ( r2_hidden(esk2_2(X16,X17),X17)
        | r1_tarski(esk2_2(X16,X17),X16)
        | X17 = k1_zfmisc_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_33,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( ~ m1_subset_1(k6_funct_2(esk4_0,esk5_0,esk6_0,k7_funct_2(esk4_0,esk5_0,esk6_0,esk7_0)),k1_zfmisc_1(k1_zfmisc_1(esk4_0)))
    | ~ r1_tarski(k3_tarski(esk7_0),k3_tarski(k6_funct_2(esk4_0,esk5_0,esk6_0,k7_funct_2(esk4_0,esk5_0,esk6_0,esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_20])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_tarski(X3,k3_tarski(k6_funct_2(X2,X1,X4,k7_funct_2(X2,X1,X4,X5))))
    | ~ v1_funct_2(X4,X2,X1)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X3,k3_tarski(X5)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_42,plain,(
    ! [X28,X29,X30,X31] :
      ( v1_xboole_0(X28)
      | v1_xboole_0(X29)
      | ~ v1_funct_1(X30)
      | ~ v1_funct_2(X30,X28,X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(X29)))
      | m1_subset_1(k6_funct_2(X28,X29,X30,X31),k1_zfmisc_1(k1_zfmisc_1(X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_funct_2])])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,X1),k1_zfmisc_1(esk4_0))
    | r1_tarski(k3_tarski(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( ~ m1_subset_1(k6_funct_2(esk4_0,esk5_0,esk6_0,k7_funct_2(esk4_0,esk5_0,esk6_0,esk7_0)),k1_zfmisc_1(k1_zfmisc_1(esk4_0)))
    | ~ m1_subset_1(k3_tarski(esk7_0),k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_21]),c_0_39])]),c_0_40]),c_0_41])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_47,plain,(
    ! [X32,X33,X34,X35] :
      ( v1_xboole_0(X32)
      | v1_xboole_0(X33)
      | ~ v1_funct_1(X34)
      | ~ v1_funct_2(X34,X32,X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | ~ m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(X32)))
      | m1_subset_1(k7_funct_2(X32,X33,X34,X35),k1_zfmisc_1(k1_zfmisc_1(X33))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_funct_2])])])).

cnf(c_0_48,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk3_2(esk7_0,X1),X2)
    | r1_tarski(k3_tarski(esk7_0),X1)
    | k1_zfmisc_1(esk4_0) != k1_zfmisc_1(X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( ~ m1_subset_1(k7_funct_2(esk4_0,esk5_0,esk6_0,esk7_0),k1_zfmisc_1(k1_zfmisc_1(esk5_0)))
    | ~ m1_subset_1(k3_tarski(esk7_0),k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_36]),c_0_37]),c_0_38])]),c_0_40]),c_0_41])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k3_tarski(esk7_0),X1)
    | k1_zfmisc_1(esk4_0) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( ~ m1_subset_1(k3_tarski(esk7_0),k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_36]),c_0_37]),c_0_38]),c_0_21])]),c_0_40]),c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k3_tarski(esk7_0),k1_zfmisc_1(X1))
    | k1_zfmisc_1(esk4_0) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_54,c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:08:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.46  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.21/0.46  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.46  #
% 0.21/0.46  # Preprocessing time       : 0.028 s
% 0.21/0.46  # Presaturation interreduction done
% 0.21/0.46  
% 0.21/0.46  # Proof found!
% 0.21/0.46  # SZS status Theorem
% 0.21/0.46  # SZS output start CNFRefutation
% 0.21/0.46  fof(t184_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))=>r1_tarski(k5_setfam_1(X1,X4),k5_setfam_1(X1,k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t184_funct_2)).
% 0.21/0.46  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.46  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.46  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.21/0.46  fof(d12_setfam_1, axiom, ![X1, X2]:(m1_setfam_1(X2,X1)<=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 0.21/0.46  fof(t182_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X1))=>(m1_setfam_1(X4,X5)=>m1_setfam_1(k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)),X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_funct_2)).
% 0.21/0.46  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.21/0.46  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.21/0.46  fof(dt_k6_funct_2, axiom, ![X1, X2, X3, X4]:((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2))))=>m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_funct_2)).
% 0.21/0.46  fof(dt_k7_funct_2, axiom, ![X1, X2, X3, X4]:((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))))=>m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_funct_2)).
% 0.21/0.46  fof(c_0_10, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))=>r1_tarski(k5_setfam_1(X1,X4),k5_setfam_1(X1,k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4))))))))), inference(assume_negation,[status(cth)],[t184_funct_2])).
% 0.21/0.46  fof(c_0_11, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.46  fof(c_0_12, plain, ![X26, X27]:((~m1_subset_1(X26,k1_zfmisc_1(X27))|r1_tarski(X26,X27))&(~r1_tarski(X26,X27)|m1_subset_1(X26,k1_zfmisc_1(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.46  fof(c_0_13, negated_conjecture, (~v1_xboole_0(esk4_0)&(~v1_xboole_0(esk5_0)&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0)))&~r1_tarski(k5_setfam_1(esk4_0,esk7_0),k5_setfam_1(esk4_0,k6_funct_2(esk4_0,esk5_0,esk6_0,k7_funct_2(esk4_0,esk5_0,esk6_0,esk7_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.21/0.46  fof(c_0_14, plain, ![X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))|k5_setfam_1(X24,X25)=k3_tarski(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.21/0.46  fof(c_0_15, plain, ![X22, X23]:((~m1_setfam_1(X23,X22)|r1_tarski(X22,k3_tarski(X23)))&(~r1_tarski(X22,k3_tarski(X23))|m1_setfam_1(X23,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).
% 0.21/0.46  fof(c_0_16, plain, ![X36, X37, X38, X39, X40]:(v1_xboole_0(X36)|(v1_xboole_0(X37)|(~v1_funct_1(X38)|~v1_funct_2(X38,X36,X37)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|(~m1_subset_1(X39,k1_zfmisc_1(k1_zfmisc_1(X36)))|(~m1_subset_1(X40,k1_zfmisc_1(X36))|(~m1_setfam_1(X39,X40)|m1_setfam_1(k6_funct_2(X36,X37,X38,k7_funct_2(X36,X37,X38,X39)),X40))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t182_funct_2])])])])).
% 0.21/0.46  cnf(c_0_17, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.46  cnf(c_0_18, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.46  cnf(c_0_19, negated_conjecture, (~r1_tarski(k5_setfam_1(esk4_0,esk7_0),k5_setfam_1(esk4_0,k6_funct_2(esk4_0,esk5_0,esk6_0,k7_funct_2(esk4_0,esk5_0,esk6_0,esk7_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.46  cnf(c_0_20, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.46  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.46  cnf(c_0_22, plain, (r1_tarski(X2,k3_tarski(X1))|~m1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.46  cnf(c_0_23, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_setfam_1(k6_funct_2(X1,X2,X3,k7_funct_2(X1,X2,X3,X4)),X5)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X5,k1_zfmisc_1(X1))|~m1_setfam_1(X4,X5)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.46  cnf(c_0_24, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.46  fof(c_0_25, plain, ![X19, X20]:((r2_hidden(esk3_2(X19,X20),X19)|r1_tarski(k3_tarski(X19),X20))&(~r1_tarski(esk3_2(X19,X20),X20)|r1_tarski(k3_tarski(X19),X20))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.21/0.46  cnf(c_0_26, negated_conjecture, (~r1_tarski(k3_tarski(esk7_0),k5_setfam_1(esk4_0,k6_funct_2(esk4_0,esk5_0,esk6_0,k7_funct_2(esk4_0,esk5_0,esk6_0,esk7_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.21/0.46  cnf(c_0_27, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r1_tarski(X3,k3_tarski(k6_funct_2(X1,X2,X4,k7_funct_2(X1,X2,X4,X5))))|~v1_funct_2(X4,X1,X2)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_setfam_1(X5,X3)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.21/0.46  cnf(c_0_28, plain, (m1_setfam_1(X2,X1)|~r1_tarski(X1,k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.46  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.46  cnf(c_0_30, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.46  fof(c_0_31, plain, ![X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X14,X13)|r1_tarski(X14,X12)|X13!=k1_zfmisc_1(X12))&(~r1_tarski(X15,X12)|r2_hidden(X15,X13)|X13!=k1_zfmisc_1(X12)))&((~r2_hidden(esk2_2(X16,X17),X17)|~r1_tarski(esk2_2(X16,X17),X16)|X17=k1_zfmisc_1(X16))&(r2_hidden(esk2_2(X16,X17),X17)|r1_tarski(esk2_2(X16,X17),X16)|X17=k1_zfmisc_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.21/0.46  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(esk4_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.21/0.46  cnf(c_0_33, plain, (r2_hidden(esk3_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.46  cnf(c_0_34, negated_conjecture, (~m1_subset_1(k6_funct_2(esk4_0,esk5_0,esk6_0,k7_funct_2(esk4_0,esk5_0,esk6_0,esk7_0)),k1_zfmisc_1(k1_zfmisc_1(esk4_0)))|~r1_tarski(k3_tarski(esk7_0),k3_tarski(k6_funct_2(esk4_0,esk5_0,esk6_0,k7_funct_2(esk4_0,esk5_0,esk6_0,esk7_0))))), inference(spm,[status(thm)],[c_0_26, c_0_20])).
% 0.21/0.46  cnf(c_0_35, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r1_tarski(X3,k3_tarski(k6_funct_2(X2,X1,X4,k7_funct_2(X2,X1,X4,X5))))|~v1_funct_2(X4,X2,X1)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X3,k3_tarski(X5))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.46  cnf(c_0_36, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.46  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.46  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.46  cnf(c_0_39, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.46  cnf(c_0_40, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.46  cnf(c_0_41, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.46  fof(c_0_42, plain, ![X28, X29, X30, X31]:(v1_xboole_0(X28)|v1_xboole_0(X29)|~v1_funct_1(X30)|~v1_funct_2(X30,X28,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(X29)))|m1_subset_1(k6_funct_2(X28,X29,X30,X31),k1_zfmisc_1(k1_zfmisc_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_funct_2])])])).
% 0.21/0.46  cnf(c_0_43, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.46  cnf(c_0_44, negated_conjecture, (r2_hidden(esk3_2(esk7_0,X1),k1_zfmisc_1(esk4_0))|r1_tarski(k3_tarski(esk7_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.46  cnf(c_0_45, negated_conjecture, (~m1_subset_1(k6_funct_2(esk4_0,esk5_0,esk6_0,k7_funct_2(esk4_0,esk5_0,esk6_0,esk7_0)),k1_zfmisc_1(k1_zfmisc_1(esk4_0)))|~m1_subset_1(k3_tarski(esk7_0),k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_21]), c_0_39])]), c_0_40]), c_0_41])).
% 0.21/0.46  cnf(c_0_46, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_subset_1(k6_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.46  fof(c_0_47, plain, ![X32, X33, X34, X35]:(v1_xboole_0(X32)|v1_xboole_0(X33)|~v1_funct_1(X34)|~v1_funct_2(X34,X32,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|~m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(X32)))|m1_subset_1(k7_funct_2(X32,X33,X34,X35),k1_zfmisc_1(k1_zfmisc_1(X33)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_funct_2])])])).
% 0.21/0.46  cnf(c_0_48, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk3_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.46  cnf(c_0_49, negated_conjecture, (r1_tarski(esk3_2(esk7_0,X1),X2)|r1_tarski(k3_tarski(esk7_0),X1)|k1_zfmisc_1(esk4_0)!=k1_zfmisc_1(X2)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.46  cnf(c_0_50, negated_conjecture, (~m1_subset_1(k7_funct_2(esk4_0,esk5_0,esk6_0,esk7_0),k1_zfmisc_1(k1_zfmisc_1(esk5_0)))|~m1_subset_1(k3_tarski(esk7_0),k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_36]), c_0_37]), c_0_38])]), c_0_40]), c_0_41])).
% 0.21/0.46  cnf(c_0_51, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_subset_1(k7_funct_2(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X2)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.46  cnf(c_0_52, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.46  cnf(c_0_53, negated_conjecture, (r1_tarski(k3_tarski(esk7_0),X1)|k1_zfmisc_1(esk4_0)!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.21/0.46  cnf(c_0_54, negated_conjecture, (~m1_subset_1(k3_tarski(esk7_0),k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_36]), c_0_37]), c_0_38]), c_0_21])]), c_0_40]), c_0_41])).
% 0.21/0.46  cnf(c_0_55, negated_conjecture, (m1_subset_1(k3_tarski(esk7_0),k1_zfmisc_1(X1))|k1_zfmisc_1(esk4_0)!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.21/0.46  cnf(c_0_56, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_54, c_0_55]), ['proof']).
% 0.21/0.46  # SZS output end CNFRefutation
% 0.21/0.46  # Proof object total steps             : 57
% 0.21/0.46  # Proof object clause steps            : 36
% 0.21/0.46  # Proof object formula steps           : 21
% 0.21/0.46  # Proof object conjectures             : 21
% 0.21/0.46  # Proof object clause conjectures      : 18
% 0.21/0.46  # Proof object formula conjectures     : 3
% 0.21/0.46  # Proof object initial clauses used    : 21
% 0.21/0.46  # Proof object initial formulas used   : 10
% 0.21/0.46  # Proof object generating inferences   : 15
% 0.21/0.46  # Proof object simplifying inferences  : 23
% 0.21/0.46  # Training examples: 0 positive, 0 negative
% 0.21/0.46  # Parsed axioms                        : 10
% 0.21/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.46  # Initial clauses                      : 24
% 0.21/0.46  # Removed in clause preprocessing      : 0
% 0.21/0.46  # Initial clauses in saturation        : 24
% 0.21/0.46  # Processed clauses                    : 696
% 0.21/0.46  # ...of these trivial                  : 2
% 0.21/0.46  # ...subsumed                          : 232
% 0.21/0.46  # ...remaining for further processing  : 462
% 0.21/0.46  # Other redundant clauses eliminated   : 0
% 0.21/0.46  # Clauses deleted for lack of memory   : 0
% 0.21/0.46  # Backward-subsumed                    : 2
% 0.21/0.46  # Backward-rewritten                   : 0
% 0.21/0.46  # Generated clauses                    : 1330
% 0.21/0.46  # ...of the previous two non-trivial   : 1312
% 0.21/0.46  # Contextual simplify-reflections      : 0
% 0.21/0.46  # Paramodulations                      : 1230
% 0.21/0.46  # Factorizations                       : 2
% 0.21/0.46  # Equation resolutions                 : 98
% 0.21/0.46  # Propositional unsat checks           : 0
% 0.21/0.46  #    Propositional check models        : 0
% 0.21/0.46  #    Propositional check unsatisfiable : 0
% 0.21/0.46  #    Propositional clauses             : 0
% 0.21/0.46  #    Propositional clauses after purity: 0
% 0.21/0.46  #    Propositional unsat core size     : 0
% 0.21/0.46  #    Propositional preprocessing time  : 0.000
% 0.21/0.46  #    Propositional encoding time       : 0.000
% 0.21/0.46  #    Propositional solver time         : 0.000
% 0.21/0.46  #    Success case prop preproc time    : 0.000
% 0.21/0.46  #    Success case prop encoding time   : 0.000
% 0.21/0.46  #    Success case prop solver time     : 0.000
% 0.21/0.46  # Current number of processed clauses  : 436
% 0.21/0.46  #    Positive orientable unit clauses  : 9
% 0.21/0.46  #    Positive unorientable unit clauses: 0
% 0.21/0.46  #    Negative unit clauses             : 13
% 0.21/0.46  #    Non-unit-clauses                  : 414
% 0.21/0.46  # Current number of unprocessed clauses: 660
% 0.21/0.46  # ...number of literals in the above   : 3768
% 0.21/0.46  # Current number of archived formulas  : 0
% 0.21/0.46  # Current number of archived clauses   : 26
% 0.21/0.46  # Clause-clause subsumption calls (NU) : 40127
% 0.21/0.46  # Rec. Clause-clause subsumption calls : 19966
% 0.21/0.46  # Non-unit clause-clause subsumptions  : 224
% 0.21/0.46  # Unit Clause-clause subsumption calls : 335
% 0.21/0.46  # Rewrite failures with RHS unbound    : 0
% 0.21/0.46  # BW rewrite match attempts            : 17
% 0.21/0.46  # BW rewrite match successes           : 0
% 0.21/0.46  # Condensation attempts                : 0
% 0.21/0.46  # Condensation successes               : 0
% 0.21/0.46  # Termbank termtop insertions          : 26470
% 0.21/0.46  
% 0.21/0.46  # -------------------------------------------------
% 0.21/0.46  # User time                : 0.112 s
% 0.21/0.46  # System time              : 0.003 s
% 0.21/0.46  # Total time               : 0.114 s
% 0.21/0.46  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
