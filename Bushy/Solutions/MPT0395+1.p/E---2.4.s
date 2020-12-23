%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t17_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:12 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 223 expanded)
%              Number of clauses        :   39 ( 103 expanded)
%              Number of leaves         :   10 (  55 expanded)
%              Depth                    :   17
%              Number of atoms          :  144 ( 660 expanded)
%              Number of equality atoms :   11 (  28 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',t6_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',t2_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',t3_subset)).

fof(t17_setfam_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_setfam_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',t17_setfam_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',dt_o_0_0_xboole_0)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',t5_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',t4_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',t1_subset)).

fof(d2_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X1)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & r1_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',d2_setfam_1)).

fof(reflexivity_r1_setfam_1,axiom,(
    ! [X1,X2] : r1_setfam_1(X1,X1) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t17_setfam_1.p',reflexivity_r1_setfam_1)).

fof(c_0_10,plain,(
    ! [X32] :
      ( ~ v1_xboole_0(X32)
      | X32 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_11,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X22,X23)
      | v1_xboole_0(X23)
      | r2_hidden(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_12,plain,(
    ! [X24,X25] :
      ( ( ~ m1_subset_1(X24,k1_zfmisc_1(X25))
        | r1_tarski(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | m1_subset_1(X24,k1_zfmisc_1(X25)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,X2)
       => r1_setfam_1(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t17_setfam_1])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_16,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & ~ r1_setfam_1(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_19,plain,(
    ! [X29,X30,X31] :
      ( ~ r2_hidden(X29,X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(X31))
      | ~ v1_xboole_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_20,plain,(
    ! [X26,X27,X28] :
      ( ~ r2_hidden(X26,X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X28))
      | m1_subset_1(X26,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_21,plain,(
    ! [X20,X21] :
      ( ~ r2_hidden(X20,X21)
      | m1_subset_1(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_22,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_23,plain,
    ( v1_xboole_0(k1_zfmisc_1(X1))
    | r2_hidden(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X9,X10,X11,X13,X14,X16] :
      ( ( r2_hidden(esk3_3(X9,X10,X11),X10)
        | ~ r2_hidden(X11,X9)
        | ~ r1_setfam_1(X9,X10) )
      & ( r1_tarski(X11,esk3_3(X9,X10,X11))
        | ~ r2_hidden(X11,X9)
        | ~ r1_setfam_1(X9,X10) )
      & ( r2_hidden(esk4_2(X13,X14),X13)
        | r1_setfam_1(X13,X14) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r1_tarski(esk4_2(X13,X14),X16)
        | r1_setfam_1(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( X1 = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_14,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk2_0))
    | r2_hidden(esk1_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_17])).

cnf(c_0_32,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k1_zfmisc_1(esk2_0) = o_0_0_xboole_0
    | r2_hidden(esk1_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r1_setfam_1(X1,X2)
    | ~ v1_xboole_0(X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r1_setfam_1(X3,X2)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(esk4_2(X3,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X2)
    | ~ r1_setfam_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( k1_zfmisc_1(esk2_0) = o_0_0_xboole_0
    | m1_subset_1(X1,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_setfam_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_40,negated_conjecture,
    ( r1_setfam_1(esk1_0,X1)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_24])).

cnf(c_0_41,plain,
    ( r1_setfam_1(X1,X2)
    | ~ r2_hidden(esk3_3(X3,X4,esk4_2(X1,X2)),X2)
    | ~ r2_hidden(esk4_2(X1,X2),X3)
    | ~ r1_setfam_1(X3,X4) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_43,negated_conjecture,
    ( k1_zfmisc_1(esk2_0) = o_0_0_xboole_0
    | m1_subset_1(esk4_2(esk1_0,X1),esk2_0)
    | r1_setfam_1(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( r1_setfam_1(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X3)
    | ~ r1_setfam_1(X3,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( k1_zfmisc_1(esk2_0) = o_0_0_xboole_0
    | r2_hidden(esk4_2(esk1_0,X1),esk2_0)
    | r1_setfam_1(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_43]),c_0_44])).

fof(c_0_47,plain,(
    ! [X19] : r1_setfam_1(X19,X19) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r1_setfam_1])])).

cnf(c_0_48,negated_conjecture,
    ( k1_zfmisc_1(esk2_0) = o_0_0_xboole_0
    | r1_setfam_1(esk1_0,X1)
    | ~ r1_setfam_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,plain,
    ( r1_setfam_1(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( k1_zfmisc_1(esk2_0) = o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(X1,o_0_0_xboole_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_50])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(X1,esk2_0)
    | ~ m1_subset_1(X2,o_0_0_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk1_0,o_0_0_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_24])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(X1,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_54]),c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( r1_setfam_1(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),esk1_0)
    | ~ r1_setfam_1(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_55])).

cnf(c_0_57,negated_conjecture,
    ( r1_setfam_1(esk1_0,X1)
    | ~ r1_setfam_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_32])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_49]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
