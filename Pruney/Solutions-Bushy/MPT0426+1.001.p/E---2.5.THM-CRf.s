%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0426+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:36 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 713 expanded)
%              Number of clauses        :   40 ( 348 expanded)
%              Number of leaves         :    7 ( 178 expanded)
%              Depth                    :   13
%              Number of atoms          :  176 (2887 expanded)
%              Number of equality atoms :   73 (1047 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(t58_setfam_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( r2_hidden(X2,X1)
       => ( r2_hidden(X2,k8_setfam_1(X1,X3))
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
             => r2_hidden(X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(c_0_7,plain,(
    ! [X22] :
      ( ~ v1_xboole_0(X22)
      | X22 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( r2_hidden(X2,X1)
         => ( r2_hidden(X2,k8_setfam_1(X1,X3))
          <=> ! [X4] :
                ( r2_hidden(X4,X3)
               => r2_hidden(X2,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t58_setfam_1])).

fof(c_0_9,plain,(
    ! [X7,X8,X9,X10,X11,X13,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X9,X8)
        | ~ r2_hidden(X10,X7)
        | r2_hidden(X9,X10)
        | X8 != k1_setfam_1(X7)
        | X7 = k1_xboole_0 )
      & ( r2_hidden(esk1_3(X7,X8,X11),X7)
        | r2_hidden(X11,X8)
        | X8 != k1_setfam_1(X7)
        | X7 = k1_xboole_0 )
      & ( ~ r2_hidden(X11,esk1_3(X7,X8,X11))
        | r2_hidden(X11,X8)
        | X8 != k1_setfam_1(X7)
        | X7 = k1_xboole_0 )
      & ( r2_hidden(esk3_2(X7,X13),X7)
        | ~ r2_hidden(esk2_2(X7,X13),X13)
        | X13 = k1_setfam_1(X7)
        | X7 = k1_xboole_0 )
      & ( ~ r2_hidden(esk2_2(X7,X13),esk3_2(X7,X13))
        | ~ r2_hidden(esk2_2(X7,X13),X13)
        | X13 = k1_setfam_1(X7)
        | X7 = k1_xboole_0 )
      & ( r2_hidden(esk2_2(X7,X13),X13)
        | ~ r2_hidden(X16,X7)
        | r2_hidden(esk2_2(X7,X13),X16)
        | X13 = k1_setfam_1(X7)
        | X7 = k1_xboole_0 )
      & ( X18 != k1_setfam_1(X17)
        | X18 = k1_xboole_0
        | X17 != k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | X19 = k1_setfam_1(X17)
        | X17 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_10,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_12,plain,(
    ! [X5,X6] :
      ( ( X6 = k1_xboole_0
        | k8_setfam_1(X5,X6) = k6_setfam_1(X5,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))) )
      & ( X6 != k1_xboole_0
        | k8_setfam_1(X5,X6) = X5
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

fof(c_0_13,negated_conjecture,(
    ! [X29] :
      ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0)))
      & r2_hidden(esk5_0,esk4_0)
      & ( r2_hidden(esk7_0,esk6_0)
        | ~ r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)) )
      & ( ~ r2_hidden(esk5_0,esk7_0)
        | ~ r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)) )
      & ( r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
        | ~ r2_hidden(X29,esk6_0)
        | r2_hidden(esk5_0,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20)))
      | k6_setfam_1(X20,X21) = k1_setfam_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,esk1_3(X2,X3,X1))
    | X3 != k1_setfam_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
    | r2_hidden(esk5_0,X1)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(esk1_3(X1,k1_setfam_1(X1),X2),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( k8_setfam_1(esk4_0,esk6_0) = k6_setfam_1(esk4_0,esk6_0)
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk7_0)
    | ~ r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X2,esk1_3(X1,k1_setfam_1(X1),X2)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( esk6_0 = o_0_0_xboole_0
    | r2_hidden(esk5_0,esk1_3(esk6_0,k1_setfam_1(esk6_0),X1))
    | r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
    | r2_hidden(X1,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k8_setfam_1(esk4_0,esk6_0) = k6_setfam_1(esk4_0,esk6_0)
    | esk6_0 = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( k6_setfam_1(esk4_0,esk6_0) = k1_setfam_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0)
    | ~ r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ r2_hidden(esk5_0,k6_setfam_1(esk4_0,esk6_0))
    | ~ r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( esk6_0 = o_0_0_xboole_0
    | r2_hidden(esk5_0,k8_setfam_1(esk4_0,esk6_0))
    | r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k8_setfam_1(esk4_0,esk6_0) = k1_setfam_1(esk6_0)
    | esk6_0 = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( esk6_0 = o_0_0_xboole_0
    | r2_hidden(esk7_0,esk6_0)
    | ~ r2_hidden(esk5_0,k6_setfam_1(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( esk6_0 = o_0_0_xboole_0
    | ~ r2_hidden(esk5_0,k6_setfam_1(esk4_0,esk6_0))
    | ~ r2_hidden(esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_15])).

cnf(c_0_36,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_31]),c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( esk6_0 = o_0_0_xboole_0
    | r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( esk6_0 = o_0_0_xboole_0
    | r2_hidden(esk7_0,esk6_0)
    | ~ r2_hidden(esk5_0,k1_setfam_1(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( esk6_0 = o_0_0_xboole_0
    | ~ r2_hidden(esk5_0,k1_setfam_1(esk6_0))
    | ~ r2_hidden(esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_28])).

cnf(c_0_40,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( esk6_0 = o_0_0_xboole_0
    | r2_hidden(esk5_0,X1)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( esk6_0 = o_0_0_xboole_0
    | r2_hidden(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( esk6_0 = o_0_0_xboole_0
    | ~ r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_44,plain,
    ( k8_setfam_1(X1,k1_xboole_0) = X1
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( esk6_0 = o_0_0_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_46,plain,
    ( k8_setfam_1(X1,o_0_0_xboole_0) = X1
    | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_15]),c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_45])).

fof(c_0_48,plain,(
    ! [X23,X24] :
      ( ~ r2_hidden(X23,X24)
      | ~ v1_xboole_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_49,negated_conjecture,
    ( k8_setfam_1(esk4_0,o_0_0_xboole_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk7_0,o_0_0_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_45]),c_0_45]),c_0_49]),c_0_50])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_11])]),
    [proof]).

%------------------------------------------------------------------------------
