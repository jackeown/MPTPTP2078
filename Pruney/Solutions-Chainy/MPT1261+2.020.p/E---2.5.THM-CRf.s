%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:29 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 521 expanded)
%              Number of clauses        :   60 ( 226 expanded)
%              Number of leaves         :   20 ( 134 expanded)
%              Depth                    :   14
%              Number of atoms          :  223 (1174 expanded)
%              Number of equality atoms :   73 ( 483 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t77_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_20,plain,(
    ! [X44,X45] : k2_xboole_0(X44,k2_xboole_0(X44,X45)) = k2_xboole_0(X44,X45) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

fof(c_0_21,plain,(
    ! [X48,X49] : k3_tarski(k2_tarski(X48,X49)) = k2_xboole_0(X48,X49) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X29,X30] : k4_xboole_0(X29,X30) = k5_xboole_0(X29,k3_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_23,plain,(
    ! [X66,X67] : k1_setfam_1(k2_tarski(X66,X67)) = k3_xboole_0(X66,X67) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X46,X47] : k2_tarski(X46,X47) = k2_tarski(X47,X46) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_27,plain,(
    ! [X42,X43] : k2_xboole_0(k3_xboole_0(X42,X43),k4_xboole_0(X42,X43)) = X42 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X50,X51] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(X50))
      | k3_subset_1(X50,X51) = k4_xboole_0(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_31,plain,(
    ! [X63,X64,X65] :
      ( ~ m1_subset_1(X64,k1_zfmisc_1(X63))
      | k7_subset_1(X63,X64,X65) = k4_xboole_0(X64,X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_32,plain,
    ( k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X2)))) = k3_tarski(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_tops_1])).

cnf(c_0_37,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_39,plain,(
    ! [X58,X59,X60] :
      ( ~ m1_subset_1(X59,k1_zfmisc_1(X58))
      | ~ m1_subset_1(X60,k1_zfmisc_1(X58))
      | k4_subset_1(X58,X59,X60) = k2_xboole_0(X59,X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_40,plain,
    ( k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,X1)))) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_25]),c_0_29]),c_0_35])).

fof(c_0_42,negated_conjecture,
    ( v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ( ~ v4_pre_topc(esk5_0,esk4_0)
      | k2_tops_1(esk4_0,esk5_0) != k7_subset_1(u1_struct_0(esk4_0),esk5_0,k1_tops_1(esk4_0,esk5_0)) )
    & ( v4_pre_topc(esk5_0,esk4_0)
      | k2_tops_1(esk4_0,esk5_0) = k7_subset_1(u1_struct_0(esk4_0),esk5_0,k1_tops_1(esk4_0,esk5_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

cnf(c_0_43,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_35])).

cnf(c_0_44,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_35])).

fof(c_0_45,plain,(
    ! [X54,X55] : m1_subset_1(k6_subset_1(X54,X55),k1_zfmisc_1(X54)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_46,plain,(
    ! [X61,X62] : k6_subset_1(X61,X62) = k4_xboole_0(X61,X62) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_47,plain,(
    ! [X78,X79] :
      ( ~ l1_pre_topc(X78)
      | ~ m1_subset_1(X79,k1_zfmisc_1(u1_struct_0(X78)))
      | k2_pre_topc(X78,X79) = k4_subset_1(u1_struct_0(X78),X79,k2_tops_1(X78,X79)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

cnf(c_0_48,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_49,plain,(
    ! [X74,X75] :
      ( ~ l1_pre_topc(X74)
      | ~ m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(X74)))
      | m1_subset_1(k2_tops_1(X74,X75),k1_zfmisc_1(u1_struct_0(X74))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_50,plain,
    ( k3_tarski(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( v4_pre_topc(esk5_0,esk4_0)
    | k2_tops_1(esk4_0,esk5_0) = k7_subset_1(u1_struct_0(esk4_0),esk5_0,k1_tops_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_tarski(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_25])).

cnf(c_0_58,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( k3_tarski(k2_tarski(X1,k3_subset_1(X1,X2))) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_43])).

cnf(c_0_60,negated_conjecture,
    ( k3_subset_1(esk5_0,k1_tops_1(esk4_0,esk5_0)) = k2_tops_1(esk4_0,esk5_0)
    | v4_pre_topc(esk5_0,esk4_0)
    | ~ m1_subset_1(k1_tops_1(esk4_0,esk5_0),k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_61,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_35])).

fof(c_0_62,plain,(
    ! [X80,X81] :
      ( ~ l1_pre_topc(X80)
      | ~ m1_subset_1(X81,k1_zfmisc_1(u1_struct_0(X80)))
      | k1_tops_1(X80,X81) = k7_subset_1(u1_struct_0(X80),X81,k2_tops_1(X80,X81)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_63,plain,
    ( k3_tarski(k2_tarski(X1,k2_tops_1(X2,X1))) = k2_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( k3_tarski(k2_tarski(esk5_0,k2_tops_1(esk4_0,esk5_0))) = esk5_0
    | v4_pre_topc(esk5_0,esk4_0)
    | ~ m1_subset_1(k1_tops_1(esk4_0,esk5_0),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_66,plain,
    ( m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_44])).

cnf(c_0_67,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_44])).

fof(c_0_69,plain,(
    ! [X39,X40,X41] :
      ( ~ r1_tarski(k4_xboole_0(X39,X40),X41)
      | r1_tarski(X39,k2_xboole_0(X40,X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_70,plain,(
    ! [X33,X34] : r1_tarski(k4_xboole_0(X33,X34),X33) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_71,plain,(
    ! [X72,X73] :
      ( ( ~ v4_pre_topc(X73,X72)
        | k2_pre_topc(X72,X73) = X73
        | ~ m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(X72)))
        | ~ l1_pre_topc(X72) )
      & ( ~ v2_pre_topc(X72)
        | k2_pre_topc(X72,X73) != X73
        | v4_pre_topc(X73,X72)
        | ~ m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(X72)))
        | ~ l1_pre_topc(X72) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_72,negated_conjecture,
    ( k2_pre_topc(esk4_0,esk5_0) = esk5_0
    | v4_pre_topc(esk5_0,esk4_0)
    | ~ m1_subset_1(k1_tops_1(esk4_0,esk5_0),k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_53])])).

cnf(c_0_73,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,plain,
    ( k7_subset_1(X1,X2,k2_tops_1(X3,X2)) = k1_tops_1(X3,X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_76,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( ~ v4_pre_topc(esk5_0,esk4_0)
    | k2_tops_1(esk4_0,esk5_0) != k7_subset_1(u1_struct_0(esk4_0),esk5_0,k1_tops_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_78,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X2) != X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( k2_pre_topc(esk4_0,esk5_0) = esk5_0
    | v4_pre_topc(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_65]),c_0_53])])).

cnf(c_0_80,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_81,plain,(
    ! [X56,X57] :
      ( ~ m1_subset_1(X57,k1_zfmisc_1(X56))
      | k3_subset_1(X56,k3_subset_1(X56,X57)) = X57 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_82,plain,
    ( k3_subset_1(X1,k2_tops_1(X2,X1)) = k1_tops_1(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k2_tops_1(X2,X1),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_74])).

fof(c_0_83,plain,(
    ! [X68,X69] :
      ( ( ~ m1_subset_1(X68,k1_zfmisc_1(X69))
        | r1_tarski(X68,X69) )
      & ( ~ r1_tarski(X68,X69)
        | m1_subset_1(X68,k1_zfmisc_1(X69)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_25]),c_0_35])).

cnf(c_0_85,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_76,c_0_35])).

cnf(c_0_86,negated_conjecture,
    ( k3_subset_1(esk5_0,k1_tops_1(esk4_0,esk5_0)) != k2_tops_1(esk4_0,esk5_0)
    | ~ v4_pre_topc(esk5_0,esk4_0)
    | ~ m1_subset_1(k1_tops_1(esk4_0,esk5_0),k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_52]),c_0_53])])).

cnf(c_0_87,negated_conjecture,
    ( v4_pre_topc(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_65]),c_0_53])])).

cnf(c_0_88,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( k3_subset_1(esk5_0,k2_tops_1(X1,esk5_0)) = k1_tops_1(X1,esk5_0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_tops_1(X1,esk5_0),k1_zfmisc_1(esk5_0))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_53])).

cnf(c_0_90,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( k3_subset_1(esk5_0,k1_tops_1(esk4_0,esk5_0)) != k2_tops_1(esk4_0,esk5_0)
    | ~ m1_subset_1(k1_tops_1(esk4_0,esk5_0),k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_93,negated_conjecture,
    ( k3_subset_1(esk5_0,k1_tops_1(X1,esk5_0)) = k2_tops_1(X1,esk5_0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_tops_1(X1,esk5_0),k1_zfmisc_1(esk5_0))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k3_tarski(k2_tarski(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk4_0,esk5_0),k1_zfmisc_1(esk5_0))
    | ~ m1_subset_1(k2_tops_1(esk4_0,esk5_0),k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_65]),c_0_53])])).

cnf(c_0_96,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(k2_pre_topc(X1,X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_63])).

cnf(c_0_97,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_98,negated_conjecture,
    ( ~ m1_subset_1(k2_tops_1(esk4_0,esk5_0),k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_73]),c_0_65]),c_0_53])])).

cnf(c_0_99,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(X2))
    | ~ v4_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_87]),c_0_65]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 3.41/3.61  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 3.41/3.61  # and selection function SelectMaxLComplexAvoidPosPred.
% 3.41/3.61  #
% 3.41/3.61  # Preprocessing time       : 0.029 s
% 3.41/3.61  
% 3.41/3.61  # Proof found!
% 3.41/3.61  # SZS status Theorem
% 3.41/3.61  # SZS output start CNFRefutation
% 3.41/3.61  fof(t6_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 3.41/3.61  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.41/3.61  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.41/3.61  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.41/3.61  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.41/3.61  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.41/3.61  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.41/3.61  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.41/3.61  fof(t77_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 3.41/3.61  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.41/3.61  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 3.41/3.61  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.41/3.61  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 3.41/3.61  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 3.41/3.61  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 3.41/3.61  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 3.41/3.61  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.41/3.61  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.41/3.61  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.41/3.61  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.41/3.61  fof(c_0_20, plain, ![X44, X45]:k2_xboole_0(X44,k2_xboole_0(X44,X45))=k2_xboole_0(X44,X45), inference(variable_rename,[status(thm)],[t6_xboole_1])).
% 3.41/3.61  fof(c_0_21, plain, ![X48, X49]:k3_tarski(k2_tarski(X48,X49))=k2_xboole_0(X48,X49), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 3.41/3.61  fof(c_0_22, plain, ![X29, X30]:k4_xboole_0(X29,X30)=k5_xboole_0(X29,k3_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 3.41/3.61  fof(c_0_23, plain, ![X66, X67]:k1_setfam_1(k2_tarski(X66,X67))=k3_xboole_0(X66,X67), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 3.41/3.61  cnf(c_0_24, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.41/3.61  cnf(c_0_25, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.41/3.61  fof(c_0_26, plain, ![X46, X47]:k2_tarski(X46,X47)=k2_tarski(X47,X46), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 3.41/3.61  fof(c_0_27, plain, ![X42, X43]:k2_xboole_0(k3_xboole_0(X42,X43),k4_xboole_0(X42,X43))=X42, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 3.41/3.61  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.41/3.61  cnf(c_0_29, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.41/3.61  fof(c_0_30, plain, ![X50, X51]:(~m1_subset_1(X51,k1_zfmisc_1(X50))|k3_subset_1(X50,X51)=k4_xboole_0(X50,X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 3.41/3.61  fof(c_0_31, plain, ![X63, X64, X65]:(~m1_subset_1(X64,k1_zfmisc_1(X63))|k7_subset_1(X63,X64,X65)=k4_xboole_0(X64,X65)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 3.41/3.61  cnf(c_0_32, plain, (k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X2))))=k3_tarski(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_25]), c_0_25])).
% 3.41/3.61  cnf(c_0_33, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 3.41/3.61  cnf(c_0_34, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.41/3.61  cnf(c_0_35, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 3.41/3.61  fof(c_0_36, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t77_tops_1])).
% 3.41/3.61  cnf(c_0_37, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.41/3.61  cnf(c_0_38, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.41/3.61  fof(c_0_39, plain, ![X58, X59, X60]:(~m1_subset_1(X59,k1_zfmisc_1(X58))|~m1_subset_1(X60,k1_zfmisc_1(X58))|k4_subset_1(X58,X59,X60)=k2_xboole_0(X59,X60)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 3.41/3.61  cnf(c_0_40, plain, (k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,X1))))=k3_tarski(k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 3.41/3.61  cnf(c_0_41, plain, (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_25]), c_0_29]), c_0_35])).
% 3.41/3.61  fof(c_0_42, negated_conjecture, ((v2_pre_topc(esk4_0)&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&((~v4_pre_topc(esk5_0,esk4_0)|k2_tops_1(esk4_0,esk5_0)!=k7_subset_1(u1_struct_0(esk4_0),esk5_0,k1_tops_1(esk4_0,esk5_0)))&(v4_pre_topc(esk5_0,esk4_0)|k2_tops_1(esk4_0,esk5_0)=k7_subset_1(u1_struct_0(esk4_0),esk5_0,k1_tops_1(esk4_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).
% 3.41/3.61  cnf(c_0_43, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_37, c_0_35])).
% 3.41/3.61  cnf(c_0_44, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_38, c_0_35])).
% 3.41/3.61  fof(c_0_45, plain, ![X54, X55]:m1_subset_1(k6_subset_1(X54,X55),k1_zfmisc_1(X54)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 3.41/3.61  fof(c_0_46, plain, ![X61, X62]:k6_subset_1(X61,X62)=k4_xboole_0(X61,X62), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 3.41/3.61  fof(c_0_47, plain, ![X78, X79]:(~l1_pre_topc(X78)|(~m1_subset_1(X79,k1_zfmisc_1(u1_struct_0(X78)))|k2_pre_topc(X78,X79)=k4_subset_1(u1_struct_0(X78),X79,k2_tops_1(X78,X79)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 3.41/3.61  cnf(c_0_48, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 3.41/3.61  fof(c_0_49, plain, ![X74, X75]:(~l1_pre_topc(X74)|~m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(X74)))|m1_subset_1(k2_tops_1(X74,X75),k1_zfmisc_1(u1_struct_0(X74)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 3.41/3.61  cnf(c_0_50, plain, (k3_tarski(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_33])).
% 3.41/3.61  cnf(c_0_51, negated_conjecture, (v4_pre_topc(esk5_0,esk4_0)|k2_tops_1(esk4_0,esk5_0)=k7_subset_1(u1_struct_0(esk4_0),esk5_0,k1_tops_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.41/3.61  cnf(c_0_52, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 3.41/3.61  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.41/3.61  cnf(c_0_54, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 3.41/3.61  cnf(c_0_55, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 3.41/3.61  cnf(c_0_56, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 3.41/3.61  cnf(c_0_57, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_tarski(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_48, c_0_25])).
% 3.41/3.61  cnf(c_0_58, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 3.41/3.61  cnf(c_0_59, plain, (k3_tarski(k2_tarski(X1,k3_subset_1(X1,X2)))=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_50, c_0_43])).
% 3.41/3.61  cnf(c_0_60, negated_conjecture, (k3_subset_1(esk5_0,k1_tops_1(esk4_0,esk5_0))=k2_tops_1(esk4_0,esk5_0)|v4_pre_topc(esk5_0,esk4_0)|~m1_subset_1(k1_tops_1(esk4_0,esk5_0),k1_zfmisc_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 3.41/3.61  cnf(c_0_61, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_35])).
% 3.41/3.61  fof(c_0_62, plain, ![X80, X81]:(~l1_pre_topc(X80)|(~m1_subset_1(X81,k1_zfmisc_1(u1_struct_0(X80)))|k1_tops_1(X80,X81)=k7_subset_1(u1_struct_0(X80),X81,k2_tops_1(X80,X81)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 3.41/3.61  cnf(c_0_63, plain, (k3_tarski(k2_tarski(X1,k2_tops_1(X2,X1)))=k2_pre_topc(X2,X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 3.41/3.61  cnf(c_0_64, negated_conjecture, (k3_tarski(k2_tarski(esk5_0,k2_tops_1(esk4_0,esk5_0)))=esk5_0|v4_pre_topc(esk5_0,esk4_0)|~m1_subset_1(k1_tops_1(esk4_0,esk5_0),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 3.41/3.61  cnf(c_0_65, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.41/3.61  cnf(c_0_66, plain, (m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_61, c_0_44])).
% 3.41/3.61  cnf(c_0_67, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 3.41/3.61  cnf(c_0_68, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_44, c_0_44])).
% 3.41/3.61  fof(c_0_69, plain, ![X39, X40, X41]:(~r1_tarski(k4_xboole_0(X39,X40),X41)|r1_tarski(X39,k2_xboole_0(X40,X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 3.41/3.61  fof(c_0_70, plain, ![X33, X34]:r1_tarski(k4_xboole_0(X33,X34),X33), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 3.41/3.61  fof(c_0_71, plain, ![X72, X73]:((~v4_pre_topc(X73,X72)|k2_pre_topc(X72,X73)=X73|~m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(X72)))|~l1_pre_topc(X72))&(~v2_pre_topc(X72)|k2_pre_topc(X72,X73)!=X73|v4_pre_topc(X73,X72)|~m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(X72)))|~l1_pre_topc(X72))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 3.41/3.61  cnf(c_0_72, negated_conjecture, (k2_pre_topc(esk4_0,esk5_0)=esk5_0|v4_pre_topc(esk5_0,esk4_0)|~m1_subset_1(k1_tops_1(esk4_0,esk5_0),k1_zfmisc_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_53])])).
% 3.41/3.61  cnf(c_0_73, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 3.41/3.61  cnf(c_0_74, plain, (k7_subset_1(X1,X2,k2_tops_1(X3,X2))=k1_tops_1(X3,X2)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 3.41/3.61  cnf(c_0_75, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 3.41/3.61  cnf(c_0_76, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 3.41/3.61  cnf(c_0_77, negated_conjecture, (~v4_pre_topc(esk5_0,esk4_0)|k2_tops_1(esk4_0,esk5_0)!=k7_subset_1(u1_struct_0(esk4_0),esk5_0,k1_tops_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.41/3.61  cnf(c_0_78, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|k2_pre_topc(X1,X2)!=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 3.41/3.61  cnf(c_0_79, negated_conjecture, (k2_pre_topc(esk4_0,esk5_0)=esk5_0|v4_pre_topc(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_65]), c_0_53])])).
% 3.41/3.61  cnf(c_0_80, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.41/3.61  fof(c_0_81, plain, ![X56, X57]:(~m1_subset_1(X57,k1_zfmisc_1(X56))|k3_subset_1(X56,k3_subset_1(X56,X57))=X57), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 3.41/3.61  cnf(c_0_82, plain, (k3_subset_1(X1,k2_tops_1(X2,X1))=k1_tops_1(X2,X1)|~l1_pre_topc(X2)|~m1_subset_1(k2_tops_1(X2,X1),k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_52, c_0_74])).
% 3.41/3.61  fof(c_0_83, plain, ![X68, X69]:((~m1_subset_1(X68,k1_zfmisc_1(X69))|r1_tarski(X68,X69))&(~r1_tarski(X68,X69)|m1_subset_1(X68,k1_zfmisc_1(X69)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 3.41/3.61  cnf(c_0_84, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_25]), c_0_35])).
% 3.41/3.61  cnf(c_0_85, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_76, c_0_35])).
% 3.41/3.61  cnf(c_0_86, negated_conjecture, (k3_subset_1(esk5_0,k1_tops_1(esk4_0,esk5_0))!=k2_tops_1(esk4_0,esk5_0)|~v4_pre_topc(esk5_0,esk4_0)|~m1_subset_1(k1_tops_1(esk4_0,esk5_0),k1_zfmisc_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_52]), c_0_53])])).
% 3.41/3.61  cnf(c_0_87, negated_conjecture, (v4_pre_topc(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), c_0_65]), c_0_53])])).
% 3.41/3.61  cnf(c_0_88, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 3.41/3.61  cnf(c_0_89, negated_conjecture, (k3_subset_1(esk5_0,k2_tops_1(X1,esk5_0))=k1_tops_1(X1,esk5_0)|~l1_pre_topc(X1)|~m1_subset_1(k2_tops_1(X1,esk5_0),k1_zfmisc_1(esk5_0))|~m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_82, c_0_53])).
% 3.41/3.61  cnf(c_0_90, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 3.41/3.61  cnf(c_0_91, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 3.41/3.61  cnf(c_0_92, negated_conjecture, (k3_subset_1(esk5_0,k1_tops_1(esk4_0,esk5_0))!=k2_tops_1(esk4_0,esk5_0)|~m1_subset_1(k1_tops_1(esk4_0,esk5_0),k1_zfmisc_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87])])).
% 3.41/3.61  cnf(c_0_93, negated_conjecture, (k3_subset_1(esk5_0,k1_tops_1(X1,esk5_0))=k2_tops_1(X1,esk5_0)|~l1_pre_topc(X1)|~m1_subset_1(k2_tops_1(X1,esk5_0),k1_zfmisc_1(esk5_0))|~m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 3.41/3.61  cnf(c_0_94, plain, (m1_subset_1(X1,k1_zfmisc_1(k3_tarski(k2_tarski(X2,X1))))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 3.41/3.61  cnf(c_0_95, negated_conjecture, (~m1_subset_1(k1_tops_1(esk4_0,esk5_0),k1_zfmisc_1(esk5_0))|~m1_subset_1(k2_tops_1(esk4_0,esk5_0),k1_zfmisc_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_65]), c_0_53])])).
% 3.41/3.61  cnf(c_0_96, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(k2_pre_topc(X1,X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_94, c_0_63])).
% 3.41/3.61  cnf(c_0_97, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 3.41/3.61  cnf(c_0_98, negated_conjecture, (~m1_subset_1(k2_tops_1(esk4_0,esk5_0),k1_zfmisc_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_73]), c_0_65]), c_0_53])])).
% 3.41/3.61  cnf(c_0_99, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(X2))|~v4_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 3.41/3.61  cnf(c_0_100, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_87]), c_0_65]), c_0_53])]), ['proof']).
% 3.41/3.61  # SZS output end CNFRefutation
% 3.41/3.61  # Proof object total steps             : 101
% 3.41/3.61  # Proof object clause steps            : 60
% 3.41/3.61  # Proof object formula steps           : 41
% 3.41/3.61  # Proof object conjectures             : 20
% 3.41/3.61  # Proof object clause conjectures      : 17
% 3.41/3.61  # Proof object formula conjectures     : 3
% 3.41/3.61  # Proof object initial clauses used    : 25
% 3.41/3.61  # Proof object initial formulas used   : 20
% 3.41/3.61  # Proof object generating inferences   : 25
% 3.41/3.61  # Proof object simplifying inferences  : 43
% 3.41/3.61  # Training examples: 0 positive, 0 negative
% 3.41/3.61  # Parsed axioms                        : 30
% 3.41/3.61  # Removed by relevancy pruning/SinE    : 0
% 3.41/3.61  # Initial clauses                      : 48
% 3.41/3.61  # Removed in clause preprocessing      : 4
% 3.41/3.61  # Initial clauses in saturation        : 44
% 3.41/3.61  # Processed clauses                    : 10785
% 3.41/3.61  # ...of these trivial                  : 162
% 3.41/3.61  # ...subsumed                          : 8775
% 3.41/3.61  # ...remaining for further processing  : 1848
% 3.41/3.61  # Other redundant clauses eliminated   : 88
% 3.41/3.61  # Clauses deleted for lack of memory   : 0
% 3.41/3.61  # Backward-subsumed                    : 300
% 3.41/3.61  # Backward-rewritten                   : 28
% 3.41/3.61  # Generated clauses                    : 272294
% 3.41/3.61  # ...of the previous two non-trivial   : 258178
% 3.41/3.61  # Contextual simplify-reflections      : 36
% 3.41/3.61  # Paramodulations                      : 271764
% 3.41/3.61  # Factorizations                       : 442
% 3.41/3.61  # Equation resolutions                 : 88
% 3.41/3.61  # Propositional unsat checks           : 0
% 3.41/3.61  #    Propositional check models        : 0
% 3.41/3.61  #    Propositional check unsatisfiable : 0
% 3.41/3.61  #    Propositional clauses             : 0
% 3.41/3.61  #    Propositional clauses after purity: 0
% 3.41/3.61  #    Propositional unsat core size     : 0
% 3.41/3.61  #    Propositional preprocessing time  : 0.000
% 3.41/3.61  #    Propositional encoding time       : 0.000
% 3.41/3.61  #    Propositional solver time         : 0.000
% 3.41/3.61  #    Success case prop preproc time    : 0.000
% 3.41/3.61  #    Success case prop encoding time   : 0.000
% 3.41/3.61  #    Success case prop solver time     : 0.000
% 3.41/3.61  # Current number of processed clauses  : 1514
% 3.41/3.61  #    Positive orientable unit clauses  : 127
% 3.41/3.61  #    Positive unorientable unit clauses: 1
% 3.41/3.61  #    Negative unit clauses             : 29
% 3.41/3.61  #    Non-unit-clauses                  : 1357
% 3.41/3.61  # Current number of unprocessed clauses: 246360
% 3.41/3.61  # ...number of literals in the above   : 1217041
% 3.41/3.61  # Current number of archived formulas  : 0
% 3.41/3.61  # Current number of archived clauses   : 332
% 3.41/3.61  # Clause-clause subsumption calls (NU) : 282743
% 3.41/3.61  # Rec. Clause-clause subsumption calls : 135093
% 3.41/3.61  # Non-unit clause-clause subsumptions  : 8021
% 3.41/3.61  # Unit Clause-clause subsumption calls : 884
% 3.41/3.61  # Rewrite failures with RHS unbound    : 0
% 3.41/3.61  # BW rewrite match attempts            : 566
% 3.41/3.61  # BW rewrite match successes           : 11
% 3.41/3.61  # Condensation attempts                : 0
% 3.41/3.61  # Condensation successes               : 0
% 3.41/3.61  # Termbank termtop insertions          : 6170435
% 3.41/3.62  
% 3.41/3.62  # -------------------------------------------------
% 3.41/3.62  # User time                : 3.159 s
% 3.41/3.62  # System time              : 0.114 s
% 3.41/3.62  # Total time               : 3.273 s
% 3.41/3.62  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
