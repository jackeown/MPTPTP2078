%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_2__t5_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:42 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 397 expanded)
%              Number of clauses        :   44 ( 163 expanded)
%              Number of leaves         :   13 (  94 expanded)
%              Depth                    :   13
%              Number of atoms          :  172 (1212 expanded)
%              Number of equality atoms :   27 ( 249 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t5_tops_2.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t5_tops_2.p',existence_m1_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t5_tops_2.p',t2_subset)).

fof(t5_tops_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ~ ( m1_setfam_1(X2,u1_struct_0(X1))
              & X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t5_tops_2.p',t5_tops_2)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t5_tops_2.p',t6_boole)).

fof(t60_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( m1_setfam_1(X2,X1)
      <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t5_tops_2.p',t60_setfam_1)).

fof(dt_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t5_tops_2.p',dt_k5_setfam_1)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t5_tops_2.p',redefinition_k5_setfam_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t5_tops_2.p',fc2_struct_0)).

fof(dt_o_2_0_tops_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => m1_subset_1(o_2_0_tops_2(X1,X2),k5_setfam_1(u1_struct_0(X1),X2)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t5_tops_2.p',dt_o_2_0_tops_2)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t5_tops_2.p',t1_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t5_tops_2.p',fc1_xboole_0)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t5_tops_2.p',d4_tarski)).

fof(c_0_13,plain,(
    ! [X40,X41,X42] :
      ( ~ r2_hidden(X40,X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(X42))
      | ~ v1_xboole_0(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_14,plain,(
    ! [X27] : m1_subset_1(esk8_1(X27),X27) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_15,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X33,X34)
      | v1_xboole_0(X34)
      | r2_hidden(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ~ ( m1_setfam_1(X2,u1_struct_0(X1))
                & X2 = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t5_tops_2])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk8_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & m1_setfam_1(esk2_0,u1_struct_0(esk1_0))
    & esk2_0 = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_21,plain,(
    ! [X45] :
      ( ~ v1_xboole_0(X45)
      | X45 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_22,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk8_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk8_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

fof(c_0_24,plain,(
    ! [X43,X44] :
      ( ( ~ m1_setfam_1(X44,X43)
        | k5_setfam_1(X43,X44) = X43
        | ~ m1_subset_1(X44,k1_zfmisc_1(k1_zfmisc_1(X43))) )
      & ( k5_setfam_1(X43,X44) != X43
        | m1_setfam_1(X44,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k1_zfmisc_1(X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).

cnf(c_0_25,negated_conjecture,
    ( m1_setfam_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20)))
      | m1_subset_1(k5_setfam_1(X20,X21),k1_zfmisc_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v1_xboole_0(esk8_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_31,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(X29)))
      | k5_setfam_1(X29,X30) = k3_tarski(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

cnf(c_0_32,plain,
    ( k5_setfam_1(X2,X1) = X2
    | ~ m1_setfam_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_35,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( esk8_1(k1_zfmisc_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_37,plain,(
    ! [X50] :
      ( v2_struct_0(X50)
      | ~ l1_struct_0(X50)
      | ~ v1_xboole_0(u1_struct_0(X50)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_38,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk1_0),k1_xboole_0) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_40,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k5_setfam_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_35])).

cnf(c_0_41,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_36])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( u1_struct_0(esk1_0) = k3_tarski(k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_34]),c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_46,plain,
    ( v1_xboole_0(k5_setfam_1(X1,X2))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_23])).

cnf(c_0_47,plain,
    ( k5_setfam_1(X1,k1_xboole_0) = k3_tarski(k1_xboole_0)
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_xboole_0(k3_tarski(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])]),c_0_45])).

fof(c_0_49,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ l1_struct_0(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
      | m1_subset_1(o_2_0_tops_2(X22,X23),k5_setfam_1(u1_struct_0(X22),X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_o_2_0_tops_2])])])).

fof(c_0_50,plain,(
    ! [X31,X32] :
      ( ~ r2_hidden(X31,X32)
      | m1_subset_1(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_51,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_41])).

cnf(c_0_52,plain,
    ( v1_xboole_0(k1_zfmisc_1(X1))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_36])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(o_2_0_tops_2(X1,X2),k5_setfam_1(u1_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_57,plain,(
    ! [X9,X10,X11,X13,X14,X15,X16,X18] :
      ( ( r2_hidden(X11,esk3_3(X9,X10,X11))
        | ~ r2_hidden(X11,X10)
        | X10 != k3_tarski(X9) )
      & ( r2_hidden(esk3_3(X9,X10,X11),X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_tarski(X9) )
      & ( ~ r2_hidden(X13,X14)
        | ~ r2_hidden(X14,X9)
        | r2_hidden(X13,X10)
        | X10 != k3_tarski(X9) )
      & ( ~ r2_hidden(esk4_2(X15,X16),X16)
        | ~ r2_hidden(esk4_2(X15,X16),X18)
        | ~ r2_hidden(X18,X15)
        | X16 = k3_tarski(X15) )
      & ( r2_hidden(esk4_2(X15,X16),esk5_2(X15,X16))
        | r2_hidden(esk4_2(X15,X16),X16)
        | X16 = k3_tarski(X15) )
      & ( r2_hidden(esk5_2(X15,X16),X15)
        | r2_hidden(esk4_2(X15,X16),X16)
        | X16 = k3_tarski(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(o_2_0_tops_2(esk1_0,X1),k5_setfam_1(k3_tarski(k1_xboole_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_xboole_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_59,negated_conjecture,
    ( k5_setfam_1(k3_tarski(k1_xboole_0),k1_xboole_0) = k3_tarski(k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_43]),c_0_43])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_xboole_0)))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_43])).

cnf(c_0_61,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_54])).

cnf(c_0_62,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(o_2_0_tops_2(esk1_0,k1_xboole_0),k3_tarski(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_56])])).

cnf(c_0_66,plain,
    ( r2_hidden(esk3_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(o_2_0_tops_2(esk1_0,k1_xboole_0),k3_tarski(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_64]),c_0_48])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_67,c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
