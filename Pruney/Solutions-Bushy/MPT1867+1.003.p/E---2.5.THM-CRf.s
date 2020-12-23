%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1867+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:56 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 157 expanded)
%              Number of clauses        :   29 (  65 expanded)
%              Number of leaves         :    9 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  144 ( 527 expanded)
%              Number of equality atoms :   18 (  55 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t35_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => v2_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(rc2_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(d5_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( r1_tarski(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v3_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = X3 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(cc1_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_xboole_0(X2)
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => v2_tex_2(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t35_tex_2])).

fof(c_0_10,plain,(
    ! [X26] :
      ( ~ v1_xboole_0(X26)
      | X26 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & v1_xboole_0(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ~ v2_tex_2(esk5_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

cnf(c_0_12,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X18] :
      ( m1_subset_1(esk3_1(X18),k1_zfmisc_1(X18))
      & v1_xboole_0(esk3_1(X18)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).

fof(c_0_15,plain,(
    ! [X12,X13,X14,X17] :
      ( ( m1_subset_1(esk1_3(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r1_tarski(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( v3_pre_topc(esk1_3(X12,X13,X14),X12)
        | ~ r1_tarski(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( k9_subset_1(u1_struct_0(X12),X13,esk1_3(X12,X13,X14)) = X14
        | ~ r1_tarski(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk2_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))
        | v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( r1_tarski(esk2_2(X12,X13),X13)
        | v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v3_pre_topc(X17,X12)
        | k9_subset_1(u1_struct_0(X12),X13,X17) != esk2_2(X12,X13)
        | v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_tex_2(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( v1_xboole_0(esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X24,X25] :
      ( ( ~ m1_subset_1(X24,k1_zfmisc_1(X25))
        | r1_tarski(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | m1_subset_1(X24,k1_zfmisc_1(X25)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_21,plain,
    ( r1_tarski(esk2_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_tex_2(k1_xboole_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

fof(c_0_25,plain,(
    ! [X23] : k3_xboole_0(X23,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_26,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X20))
      | k9_subset_1(X20,X21,X22) = k3_xboole_0(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,plain,
    ( esk3_1(X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_19])).

fof(c_0_29,plain,(
    ! [X5,X6] :
      ( ~ v1_xboole_0(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | v1_xboole_0(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk2_2(esk4_0,k1_xboole_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk2_2(esk4_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_13,c_0_17])).

cnf(c_0_38,plain,
    ( v2_tex_2(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != esk2_2(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,plain,
    ( k9_subset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(esk2_2(esk4_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_41,plain,
    ( v2_tex_2(X1,X2)
    | esk2_2(X2,X1) != k1_xboole_0
    | ~ v3_pre_topc(k1_xboole_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_34])])).

cnf(c_0_42,negated_conjecture,
    ( esk2_2(esk4_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_40])).

fof(c_0_43,plain,(
    ! [X7,X8] :
      ( ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ v1_xboole_0(X8)
      | v3_pre_topc(X8,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tops_1])])])).

cnf(c_0_44,negated_conjecture,
    ( ~ v3_pre_topc(k1_xboole_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_23]),c_0_34])]),c_0_24])).

cnf(c_0_45,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_23]),c_0_46]),c_0_34]),c_0_37])]),
    [proof]).

%------------------------------------------------------------------------------
