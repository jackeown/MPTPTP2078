%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_1__t109_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:26 EDT 2019

% Result     : Theorem 152.20s
% Output     : CNFRefutation 152.20s
% Verified   : 
% Statistics : Number of formulae       :  141 (4523 expanded)
%              Number of clauses        :  106 (2136 expanded)
%              Number of leaves         :   17 (1154 expanded)
%              Depth                    :   18
%              Number of atoms          :  221 (7524 expanded)
%              Number of equality atoms :   90 (2523 expanded)
%              Maximal formula depth    :   11 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t109_tops_1.p',t2_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t109_tops_1.p',commutativity_k3_xboole_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t109_tops_1.p',redefinition_k9_subset_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t109_tops_1.p',existence_m1_subset_1)).

fof(t109_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v6_tops_1(X2,X1)
                  & v6_tops_1(X3,X1) )
               => v6_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t109_tops_1.p',t109_tops_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t109_tops_1.p',dt_k9_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t109_tops_1.p',d5_subset_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t109_tops_1.p',t3_boole)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t109_tops_1.p',dt_k3_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t109_tops_1.p',involutiveness_k3_subset_1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t109_tops_1.p',commutativity_k9_subset_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t109_tops_1.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t109_tops_1.p',commutativity_k2_xboole_0)).

fof(t54_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t109_tops_1.p',t54_xboole_1)).

fof(t101_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_tops_1(X2,X1)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t109_tops_1.p',t101_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t109_tops_1.p',redefinition_k4_subset_1)).

fof(t108_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v5_tops_1(X2,X1)
                  & v5_tops_1(X3,X1) )
               => v5_tops_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t109_tops_1.p',t108_tops_1)).

fof(c_0_17,plain,(
    ! [X58] : k3_xboole_0(X58,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_18,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k3_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_19,plain,(
    ! [X47,X48,X49] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(X47))
      | k9_subset_1(X47,X48,X49) = k3_xboole_0(X48,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_20,plain,(
    ! [X32] : m1_subset_1(esk6_1(X32),X32) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v6_tops_1(X2,X1)
                    & v6_tops_1(X3,X1) )
                 => v6_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t109_tops_1])).

fof(c_0_22,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X26))
      | m1_subset_1(k9_subset_1(X26,X27,X28),k1_zfmisc_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk6_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v6_tops_1(esk2_0,esk1_0)
    & v6_tops_1(esk3_0,esk1_0)
    & ~ v6_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_28,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( k9_subset_1(X1,X2,esk6_1(k1_zfmisc_1(X1))) = k3_xboole_0(X2,esk6_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | k3_subset_1(X19,X20) = k4_xboole_0(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_33,plain,
    ( m1_subset_1(k9_subset_1(X1,X2,esk6_1(k1_zfmisc_1(X1))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_26])).

cnf(c_0_34,plain,
    ( k9_subset_1(X1,k1_xboole_0,esk6_1(k1_zfmisc_1(X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_35,plain,(
    ! [X61] : k4_xboole_0(X61,k1_xboole_0) = X61 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_36,negated_conjecture,
    ( k3_xboole_0(X1,esk3_0) = k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_31])).

fof(c_0_37,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | m1_subset_1(k3_subset_1(X21,X22),k1_zfmisc_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_38,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),k1_xboole_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_36])).

cnf(c_0_43,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_46,plain,(
    ! [X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | k3_subset_1(X42,k3_subset_1(X42,X43)) = X43 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_39]),c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k1_xboole_0) = u1_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_45]),c_0_40])).

fof(c_0_50,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X16))
      | k9_subset_1(X16,X17,X18) = k9_subset_1(X16,X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_51,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_52,plain,(
    ! [X55] : k2_xboole_0(X55,k1_xboole_0) = X55 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_53,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_54,negated_conjecture,
    ( k3_xboole_0(X1,esk2_0) = k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_47])).

cnf(c_0_55,plain,
    ( k9_subset_1(X1,X2,X1) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_45]),c_0_49])).

cnf(c_0_57,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_58,plain,(
    ! [X68,X69,X70] : k4_xboole_0(X68,k3_xboole_0(X69,X70)) = k2_xboole_0(k4_xboole_0(X68,X69),k4_xboole_0(X68,X70)) ),
    inference(variable_rename,[status(thm)],[t54_xboole_1])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,X1) = k3_subset_1(X1,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_48])).

cnf(c_0_60,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_39]),c_0_44])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( k3_xboole_0(esk2_0,X1) = k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) = k9_subset_1(esk2_0,X1,esk2_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),X1,u1_struct_0(esk1_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),X1) = k9_subset_1(u1_struct_0(esk1_0),X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_56])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_69,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,plain,
    ( k9_subset_1(X1,X2,X1) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_55])).

cnf(c_0_71,plain,
    ( k9_subset_1(X1,X1,X2) = k9_subset_1(X1,X2,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_48])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_47])).

cnf(c_0_73,negated_conjecture,
    ( k3_xboole_0(X1,k9_subset_1(u1_struct_0(esk1_0),X2,esk3_0)) = k9_subset_1(u1_struct_0(esk1_0),X1,k9_subset_1(u1_struct_0(esk1_0),X2,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_41])).

cnf(c_0_74,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0) = k9_subset_1(esk3_0,X1,esk3_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_55])).

cnf(c_0_75,negated_conjecture,
    ( k3_xboole_0(esk2_0,X1) = k9_subset_1(esk2_0,X1,esk2_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_77,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_78,plain,
    ( k9_subset_1(X1,X1,X2) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0),X2) = k9_subset_1(u1_struct_0(esk1_0),X2,k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( k3_xboole_0(X1,k9_subset_1(esk3_0,X2,esk3_0)) = k9_subset_1(u1_struct_0(esk1_0),X1,k9_subset_1(esk3_0,X2,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74]),c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( k9_subset_1(X1,esk2_0,X1) = k9_subset_1(esk2_0,X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),X1,k9_subset_1(u1_struct_0(esk1_0),X2,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_72])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(esk1_0),k9_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),X1)) = k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_76])).

cnf(c_0_84,plain,
    ( k4_xboole_0(X1,k9_subset_1(X1,X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),k9_subset_1(esk2_0,X1,esk2_0),X2) = k9_subset_1(u1_struct_0(esk1_0),X2,k9_subset_1(esk2_0,X1,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_64]),c_0_64])).

cnf(c_0_86,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),X1,k9_subset_1(esk2_0,esk3_0,esk2_0)) = k9_subset_1(k9_subset_1(esk2_0,esk3_0,esk2_0),X1,k9_subset_1(esk2_0,esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_55])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(esk1_0),k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_72])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),X1,k9_subset_1(esk2_0,X2,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_82,c_0_64])).

cnf(c_0_89,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),X1))) = k9_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_76])).

cnf(c_0_90,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),X1)) = k4_xboole_0(u1_struct_0(esk1_0),X1) ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0))) = k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_72])).

fof(c_0_92,plain,(
    ! [X50,X51] :
      ( ( ~ v6_tops_1(X51,X50)
        | v5_tops_1(k3_subset_1(u1_struct_0(X50),X51),X50)
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))
        | ~ l1_pre_topc(X50) )
      & ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X50),X51),X50)
        | v6_tops_1(X51,X50)
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))
        | ~ l1_pre_topc(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t101_tops_1])])])])).

fof(c_0_93,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(X44))
      | ~ m1_subset_1(X46,k1_zfmisc_1(X44))
      | k4_subset_1(X44,X45,X46) = k2_xboole_0(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_94,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(esk1_0),esk2_0) = k3_subset_1(u1_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_47])).

cnf(c_0_95,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),k9_subset_1(esk2_0,esk3_0,esk2_0),X1) = k9_subset_1(k9_subset_1(esk2_0,esk3_0,esk2_0),X1,k9_subset_1(esk2_0,esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_96,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),X1,k9_subset_1(esk2_0,esk2_0,esk3_0)) = k9_subset_1(k9_subset_1(esk2_0,esk2_0,esk3_0),X1,k9_subset_1(esk2_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_71]),c_0_71]),c_0_71])).

cnf(c_0_97,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(esk1_0),k9_subset_1(esk2_0,X1,esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(esk2_0,X1,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_64]),c_0_64])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(k9_subset_1(k9_subset_1(esk2_0,esk3_0,esk2_0),X1,k9_subset_1(esk2_0,esk3_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_86])).

cnf(c_0_99,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k4_xboole_0(u1_struct_0(esk1_0),X1)) = k9_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),X1) ),
    inference(rw,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_100,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(esk2_0,X1,esk2_0))) = k9_subset_1(esk2_0,X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_64]),c_0_64])).

cnf(c_0_101,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk3_0,X1) = k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_31])).

fof(c_0_102,plain,(
    ! [X52,X53,X54] :
      ( ~ v2_pre_topc(X52)
      | ~ l1_pre_topc(X52)
      | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
      | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X52)))
      | ~ v5_tops_1(X53,X52)
      | ~ v5_tops_1(X54,X52)
      | v5_tops_1(k4_subset_1(u1_struct_0(X52),X53,X54),X52) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_tops_1])])])).

cnf(c_0_103,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v6_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_104,negated_conjecture,
    ( v6_tops_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_105,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_106,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_31])).

cnf(c_0_108,negated_conjecture,
    ( k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k4_xboole_0(u1_struct_0(esk1_0),X1)) = k4_xboole_0(u1_struct_0(esk1_0),k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_94]),c_0_63])).

cnf(c_0_109,plain,
    ( k4_xboole_0(X1,k9_subset_1(X1,X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_70])).

cnf(c_0_110,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),k9_subset_1(esk2_0,esk2_0,esk3_0),X1) = k9_subset_1(k9_subset_1(esk2_0,esk2_0,esk3_0),X1,k9_subset_1(esk2_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_71]),c_0_71]),c_0_71])).

cnf(c_0_111,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(esk1_0),k9_subset_1(k9_subset_1(esk2_0,esk2_0,esk3_0),k9_subset_1(esk2_0,esk2_0,esk3_0),u1_struct_0(esk1_0))) = k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(k9_subset_1(esk2_0,esk2_0,esk3_0),k9_subset_1(esk2_0,esk2_0,esk3_0),u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_96]),c_0_71]),c_0_71])).

cnf(c_0_112,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(esk1_0),k9_subset_1(esk2_0,esk2_0,X1)) = k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(esk2_0,esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_71])).

cnf(c_0_113,negated_conjecture,
    ( m1_subset_1(k9_subset_1(k9_subset_1(esk2_0,esk2_0,esk3_0),X1,k9_subset_1(esk2_0,esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_71]),c_0_71])).

cnf(c_0_114,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k9_subset_1(esk2_0,X1,esk2_0)) = k9_subset_1(esk2_0,X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_97]),c_0_100])).

cnf(c_0_115,negated_conjecture,
    ( ~ v6_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_116,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0) = k9_subset_1(esk2_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_64])).

cnf(c_0_117,plain,
    ( v5_tops_1(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_tops_1(X2,X1)
    | ~ v5_tops_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_118,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_119,negated_conjecture,
    ( v5_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_31]),c_0_104]),c_0_105])])).

cnf(c_0_120,negated_conjecture,
    ( v6_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_121,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk3_0)) = k2_xboole_0(X1,k3_subset_1(u1_struct_0(esk1_0),esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_122,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_47])).

cnf(c_0_123,negated_conjecture,
    ( k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k4_xboole_0(u1_struct_0(esk1_0),X1)) = k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_108,c_0_87])).

cnf(c_0_124,plain,
    ( v6_tops_1(X2,X1)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_125,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(k9_subset_1(esk2_0,esk2_0,esk3_0),k9_subset_1(esk2_0,esk2_0,esk3_0),u1_struct_0(esk1_0))) = k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(esk2_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_71]),c_0_111]),c_0_112])).

cnf(c_0_126,negated_conjecture,
    ( m1_subset_1(k9_subset_1(k9_subset_1(esk2_0,esk2_0,esk3_0),k9_subset_1(esk2_0,esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_113,c_0_71])).

cnf(c_0_127,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k9_subset_1(esk2_0,esk2_0,X1)) = k9_subset_1(esk2_0,esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_114,c_0_71])).

cnf(c_0_128,negated_conjecture,
    ( ~ v6_tops_1(k9_subset_1(esk2_0,esk3_0,esk2_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_129,negated_conjecture,
    ( v5_tops_1(k4_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk3_0)),esk1_0)
    | ~ v5_tops_1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_107]),c_0_105]),c_0_118])]),c_0_119])])).

cnf(c_0_130,negated_conjecture,
    ( v5_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_47]),c_0_120]),c_0_105])])).

cnf(c_0_131,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk3_0)) = k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_132,negated_conjecture,
    ( k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k4_xboole_0(u1_struct_0(esk1_0),X1)) = k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(esk2_0,X1,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_123,c_0_64])).

cnf(c_0_133,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(esk1_0),esk3_0) = k3_subset_1(u1_struct_0(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_31])).

cnf(c_0_134,negated_conjecture,
    ( v6_tops_1(k9_subset_1(k9_subset_1(esk2_0,esk2_0,esk3_0),k9_subset_1(esk2_0,esk2_0,esk3_0),u1_struct_0(esk1_0)),esk1_0)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(esk2_0,esk2_0,esk3_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_126]),c_0_105])])).

cnf(c_0_135,negated_conjecture,
    ( k9_subset_1(k9_subset_1(esk2_0,esk2_0,esk3_0),k9_subset_1(esk2_0,esk2_0,esk3_0),u1_struct_0(esk1_0)) = k9_subset_1(esk2_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_127]),c_0_71])).

cnf(c_0_136,negated_conjecture,
    ( ~ v6_tops_1(k9_subset_1(esk2_0,esk2_0,esk3_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_128,c_0_71])).

cnf(c_0_137,negated_conjecture,
    ( v5_tops_1(k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk3_0)),esk1_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_122]),c_0_130])]),c_0_131])).

cnf(c_0_138,negated_conjecture,
    ( k2_xboole_0(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk3_0)) = k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(esk2_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_71])).

cnf(c_0_139,negated_conjecture,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(esk2_0,esk2_0,esk3_0)),esk1_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_134,c_0_135]),c_0_136])).

cnf(c_0_140,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_137,c_0_138]),c_0_139]),
    [proof]).
%------------------------------------------------------------------------------
