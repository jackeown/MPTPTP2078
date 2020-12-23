%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:29 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 503 expanded)
%              Number of clauses        :   63 ( 211 expanded)
%              Number of leaves         :   21 ( 126 expanded)
%              Depth                    :   12
%              Number of atoms          :  217 (1311 expanded)
%              Number of equality atoms :   73 ( 430 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t77_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

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

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

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

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_tops_1])).

fof(c_0_22,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_23,plain,(
    ! [X53,X54] : k1_setfam_1(k2_tarski(X53,X54)) = k3_xboole_0(X53,X54) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_24,plain,(
    ! [X63,X64] :
      ( ~ l1_pre_topc(X63)
      | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))
      | k2_tops_1(X63,X64) = k2_tops_1(X63,k3_subset_1(u1_struct_0(X63),X64)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

fof(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ v4_pre_topc(esk3_0,esk2_0)
      | k2_tops_1(esk2_0,esk3_0) != k7_subset_1(u1_struct_0(esk2_0),esk3_0,k1_tops_1(esk2_0,esk3_0)) )
    & ( v4_pre_topc(esk3_0,esk2_0)
      | k2_tops_1(esk2_0,esk3_0) = k7_subset_1(u1_struct_0(esk2_0),esk3_0,k1_tops_1(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_26,plain,(
    ! [X55,X56] :
      ( ( ~ m1_subset_1(X55,k1_zfmisc_1(X56))
        | r1_tarski(X55,X56) )
      & ( ~ r1_tarski(X55,X56)
        | m1_subset_1(X55,k1_zfmisc_1(X56)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_27,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | m1_subset_1(k3_subset_1(X37,X38),k1_zfmisc_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_28,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(X48))
      | k7_subset_1(X48,X49,X50) = k4_xboole_0(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X59,X60] :
      ( ~ l1_pre_topc(X59)
      | ~ m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))
      | m1_subset_1(k2_tops_1(X59,X60),k1_zfmisc_1(u1_struct_0(X59))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_32,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X67,X68] :
      ( ~ l1_pre_topc(X67)
      | ~ m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))
      | k1_tops_1(X67,X68) = k7_subset_1(u1_struct_0(X67),X68,k2_tops_1(X67,X68)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_38,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_40,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | k3_subset_1(X35,X36) = k4_xboole_0(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_41,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X43))
      | ~ m1_subset_1(X45,k1_zfmisc_1(X43))
      | k4_subset_1(X43,X44,X45) = k2_xboole_0(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_42,plain,(
    ! [X32,X33] : k3_tarski(k2_tarski(X32,X33)) = k2_xboole_0(X32,X33) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_43,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( k2_tops_1(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0)) = k2_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_45,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_46,plain,(
    ! [X16,X17] : r1_tarski(k4_xboole_0(X16,X17),X16) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_47,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_50,plain,(
    ! [X26,X27] : k2_xboole_0(k3_xboole_0(X26,X27),k4_xboole_0(X26,X27)) = X26 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_51,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_34])])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_33])).

fof(c_0_56,plain,(
    ! [X65,X66] :
      ( ~ l1_pre_topc(X65)
      | ~ m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))
      | k2_pre_topc(X65,X66) = k4_subset_1(u1_struct_0(X65),X66,k2_tops_1(X65,X66)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

cnf(c_0_57,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),esk3_0,k2_tops_1(esk2_0,esk3_0)) = k1_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_33]),c_0_34])])).

cnf(c_0_59,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),esk3_0,X1) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_33])).

fof(c_0_60,plain,(
    ! [X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X41))
      | k3_subset_1(X41,k3_subset_1(X41,X42)) = X42 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_61,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_39])).

fof(c_0_62,plain,(
    ! [X28,X29] : k2_xboole_0(X28,k2_xboole_0(X28,X29)) = k2_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

cnf(c_0_63,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk2_0)
    | k2_tops_1(esk2_0,esk3_0) = k7_subset_1(u1_struct_0(esk2_0),esk3_0,k1_tops_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_65,plain,(
    ! [X30,X31] : k2_tarski(X30,X31) = k2_tarski(X31,X30) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_66,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_tarski(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_68,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_69,plain,(
    ! [X57,X58] :
      ( ( ~ v4_pre_topc(X58,X57)
        | k2_pre_topc(X57,X58) = X58
        | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))
        | ~ l1_pre_topc(X57) )
      & ( ~ v2_pre_topc(X57)
        | k2_pre_topc(X57,X58) != X58
        | v4_pre_topc(X58,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))
        | ~ l1_pre_topc(X57) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

fof(c_0_70,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(k4_xboole_0(X23,X24),X25)
      | r1_tarski(X23,k2_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_71,negated_conjecture,
    ( ~ v4_pre_topc(esk3_0,esk2_0)
    | k2_tops_1(esk2_0,esk3_0) != k7_subset_1(u1_struct_0(esk2_0),esk3_0,k1_tops_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_72,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_57,c_0_39])).

cnf(c_0_73,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,k2_tops_1(esk2_0,esk3_0)))) = k1_tops_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_74,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_54])).

fof(c_0_76,plain,(
    ! [X61,X62] :
      ( ~ v2_pre_topc(X61)
      | ~ l1_pre_topc(X61)
      | ~ m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))
      | v4_pre_topc(k2_pre_topc(X61,X62),X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_77,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_78,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_52]),c_0_30]),c_0_39])).

cnf(c_0_79,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,k1_tops_1(esk2_0,esk3_0)))) = k2_tops_1(esk2_0,esk3_0)
    | v4_pre_topc(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_64,c_0_59])).

cnf(c_0_80,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_81,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk2_0),X1,k2_tops_1(esk2_0,esk3_0)) = k3_tarski(k2_tarski(X1,k2_tops_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_82,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk2_0),esk3_0,k2_tops_1(esk2_0,esk3_0)) = k2_pre_topc(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_33]),c_0_34])])).

cnf(c_0_83,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_85,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,k1_tops_1(esk2_0,esk3_0)))) != k2_tops_1(esk2_0,esk3_0)
    | ~ v4_pre_topc(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_59])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_87,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_54])).

cnf(c_0_88,negated_conjecture,
    ( k3_subset_1(esk3_0,k2_tops_1(esk2_0,esk3_0)) = k1_tops_1(esk2_0,esk3_0)
    | ~ r1_tarski(k2_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_75])).

cnf(c_0_89,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_90,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_91,plain,
    ( k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X2)))) = k3_tarski(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_52]),c_0_52]),c_0_52])).

cnf(c_0_92,negated_conjecture,
    ( k3_tarski(k2_tarski(k2_tops_1(esk2_0,esk3_0),k1_setfam_1(k2_tarski(esk3_0,k1_tops_1(esk2_0,esk3_0))))) = esk3_0
    | v4_pre_topc(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_93,negated_conjecture,
    ( k3_tarski(k2_tarski(esk3_0,k2_tops_1(esk2_0,esk3_0))) = k2_pre_topc(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_33]),c_0_82])).

cnf(c_0_94,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk3_0) = esk3_0
    | ~ v4_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_33]),c_0_34])])).

cnf(c_0_95,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_52]),c_0_39])).

cnf(c_0_96,negated_conjecture,
    ( k3_subset_1(esk3_0,k1_tops_1(esk2_0,esk3_0)) != k2_tops_1(esk2_0,esk3_0)
    | ~ v4_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_75]),c_0_86])])).

cnf(c_0_97,negated_conjecture,
    ( k3_subset_1(esk3_0,k1_tops_1(esk2_0,esk3_0)) = k2_tops_1(esk2_0,esk3_0)
    | ~ r1_tarski(k2_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_98,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_33]),c_0_90]),c_0_34])])).

cnf(c_0_99,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk3_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_80]),c_0_93]),c_0_94])).

cnf(c_0_100,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_72])).

cnf(c_0_101,negated_conjecture,
    ( ~ v4_pre_topc(esk3_0,esk2_0)
    | ~ r1_tarski(k2_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk2_0,esk3_0),k2_pre_topc(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_93])).

cnf(c_0_104,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_102])])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_99]),c_0_104]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:20:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.19/0.45  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.029 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(t77_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 0.19/0.45  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.45  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.45  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 0.19/0.45  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.45  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.19/0.45  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.19/0.45  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 0.19/0.45  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 0.19/0.45  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.45  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.19/0.45  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.45  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.45  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.19/0.45  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 0.19/0.45  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.19/0.45  fof(t6_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 0.19/0.45  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.45  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.19/0.45  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.19/0.45  fof(fc1_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_pre_topc(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 0.19/0.45  fof(c_0_21, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t77_tops_1])).
% 0.19/0.45  fof(c_0_22, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.45  fof(c_0_23, plain, ![X53, X54]:k1_setfam_1(k2_tarski(X53,X54))=k3_xboole_0(X53,X54), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.45  fof(c_0_24, plain, ![X63, X64]:(~l1_pre_topc(X63)|(~m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))|k2_tops_1(X63,X64)=k2_tops_1(X63,k3_subset_1(u1_struct_0(X63),X64)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 0.19/0.45  fof(c_0_25, negated_conjecture, ((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~v4_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)!=k7_subset_1(u1_struct_0(esk2_0),esk3_0,k1_tops_1(esk2_0,esk3_0)))&(v4_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)=k7_subset_1(u1_struct_0(esk2_0),esk3_0,k1_tops_1(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.19/0.45  fof(c_0_26, plain, ![X55, X56]:((~m1_subset_1(X55,k1_zfmisc_1(X56))|r1_tarski(X55,X56))&(~r1_tarski(X55,X56)|m1_subset_1(X55,k1_zfmisc_1(X56)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.45  fof(c_0_27, plain, ![X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|m1_subset_1(k3_subset_1(X37,X38),k1_zfmisc_1(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.19/0.45  fof(c_0_28, plain, ![X48, X49, X50]:(~m1_subset_1(X49,k1_zfmisc_1(X48))|k7_subset_1(X48,X49,X50)=k4_xboole_0(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.19/0.45  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.45  cnf(c_0_30, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.45  fof(c_0_31, plain, ![X59, X60]:(~l1_pre_topc(X59)|~m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))|m1_subset_1(k2_tops_1(X59,X60),k1_zfmisc_1(u1_struct_0(X59)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 0.19/0.45  cnf(c_0_32, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.45  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.45  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.45  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.45  cnf(c_0_36, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.45  fof(c_0_37, plain, ![X67, X68]:(~l1_pre_topc(X67)|(~m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))|k1_tops_1(X67,X68)=k7_subset_1(u1_struct_0(X67),X68,k2_tops_1(X67,X68)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 0.19/0.45  cnf(c_0_38, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.45  cnf(c_0_39, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.45  fof(c_0_40, plain, ![X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(X35))|k3_subset_1(X35,X36)=k4_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.45  fof(c_0_41, plain, ![X43, X44, X45]:(~m1_subset_1(X44,k1_zfmisc_1(X43))|~m1_subset_1(X45,k1_zfmisc_1(X43))|k4_subset_1(X43,X44,X45)=k2_xboole_0(X44,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.19/0.45  fof(c_0_42, plain, ![X32, X33]:k3_tarski(k2_tarski(X32,X33))=k2_xboole_0(X32,X33), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.45  cnf(c_0_43, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.45  cnf(c_0_44, negated_conjecture, (k2_tops_1(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0))=k2_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.19/0.45  cnf(c_0_45, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.45  fof(c_0_46, plain, ![X16, X17]:r1_tarski(k4_xboole_0(X16,X17),X16), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.45  cnf(c_0_47, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.45  cnf(c_0_48, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.45  cnf(c_0_49, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.45  fof(c_0_50, plain, ![X26, X27]:k2_xboole_0(k3_xboole_0(X26,X27),k4_xboole_0(X26,X27))=X26, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.19/0.45  cnf(c_0_51, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.45  cnf(c_0_52, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.45  cnf(c_0_53, negated_conjecture, (m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_34])])).
% 0.19/0.45  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.45  cnf(c_0_55, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_45, c_0_33])).
% 0.19/0.45  fof(c_0_56, plain, ![X65, X66]:(~l1_pre_topc(X65)|(~m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))|k2_pre_topc(X65,X66)=k4_subset_1(u1_struct_0(X65),X66,k2_tops_1(X65,X66)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 0.19/0.45  cnf(c_0_57, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.45  cnf(c_0_58, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),esk3_0,k2_tops_1(esk2_0,esk3_0))=k1_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_33]), c_0_34])])).
% 0.19/0.45  cnf(c_0_59, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),esk3_0,X1)=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_48, c_0_33])).
% 0.19/0.45  fof(c_0_60, plain, ![X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(X41))|k3_subset_1(X41,k3_subset_1(X41,X42))=X42), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.19/0.45  cnf(c_0_61, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_49, c_0_39])).
% 0.19/0.45  fof(c_0_62, plain, ![X28, X29]:k2_xboole_0(X28,k2_xboole_0(X28,X29))=k2_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t6_xboole_1])).
% 0.19/0.45  cnf(c_0_63, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.45  cnf(c_0_64, negated_conjecture, (v4_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)=k7_subset_1(u1_struct_0(esk2_0),esk3_0,k1_tops_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.45  fof(c_0_65, plain, ![X30, X31]:k2_tarski(X30,X31)=k2_tarski(X31,X30), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.45  cnf(c_0_66, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_tarski(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.45  cnf(c_0_67, negated_conjecture, (m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.19/0.45  cnf(c_0_68, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.45  fof(c_0_69, plain, ![X57, X58]:((~v4_pre_topc(X58,X57)|k2_pre_topc(X57,X58)=X58|~m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))|~l1_pre_topc(X57))&(~v2_pre_topc(X57)|k2_pre_topc(X57,X58)!=X58|v4_pre_topc(X58,X57)|~m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))|~l1_pre_topc(X57))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.19/0.45  fof(c_0_70, plain, ![X23, X24, X25]:(~r1_tarski(k4_xboole_0(X23,X24),X25)|r1_tarski(X23,k2_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.19/0.45  cnf(c_0_71, negated_conjecture, (~v4_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)!=k7_subset_1(u1_struct_0(esk2_0),esk3_0,k1_tops_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.45  cnf(c_0_72, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_57, c_0_39])).
% 0.19/0.45  cnf(c_0_73, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,k2_tops_1(esk2_0,esk3_0))))=k1_tops_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.45  cnf(c_0_74, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.45  cnf(c_0_75, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_61, c_0_54])).
% 0.19/0.45  fof(c_0_76, plain, ![X61, X62]:(~v2_pre_topc(X61)|~l1_pre_topc(X61)|~m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))|v4_pre_topc(k2_pre_topc(X61,X62),X61)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).
% 0.19/0.45  cnf(c_0_77, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.45  cnf(c_0_78, plain, (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_52]), c_0_30]), c_0_39])).
% 0.19/0.45  cnf(c_0_79, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,k1_tops_1(esk2_0,esk3_0))))=k2_tops_1(esk2_0,esk3_0)|v4_pre_topc(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_64, c_0_59])).
% 0.19/0.45  cnf(c_0_80, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.45  cnf(c_0_81, negated_conjecture, (k4_subset_1(u1_struct_0(esk2_0),X1,k2_tops_1(esk2_0,esk3_0))=k3_tarski(k2_tarski(X1,k2_tops_1(esk2_0,esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.45  cnf(c_0_82, negated_conjecture, (k4_subset_1(u1_struct_0(esk2_0),esk3_0,k2_tops_1(esk2_0,esk3_0))=k2_pre_topc(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_33]), c_0_34])])).
% 0.19/0.45  cnf(c_0_83, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.45  cnf(c_0_84, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.45  cnf(c_0_85, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,k1_tops_1(esk2_0,esk3_0))))!=k2_tops_1(esk2_0,esk3_0)|~v4_pre_topc(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_71, c_0_59])).
% 0.19/0.45  cnf(c_0_86, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.45  cnf(c_0_87, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_74, c_0_54])).
% 0.19/0.45  cnf(c_0_88, negated_conjecture, (k3_subset_1(esk3_0,k2_tops_1(esk2_0,esk3_0))=k1_tops_1(esk2_0,esk3_0)|~r1_tarski(k2_tops_1(esk2_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_73, c_0_75])).
% 0.19/0.45  cnf(c_0_89, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.19/0.45  cnf(c_0_90, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.45  cnf(c_0_91, plain, (k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X2))))=k3_tarski(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_52]), c_0_52]), c_0_52])).
% 0.19/0.45  cnf(c_0_92, negated_conjecture, (k3_tarski(k2_tarski(k2_tops_1(esk2_0,esk3_0),k1_setfam_1(k2_tarski(esk3_0,k1_tops_1(esk2_0,esk3_0)))))=esk3_0|v4_pre_topc(esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 0.19/0.45  cnf(c_0_93, negated_conjecture, (k3_tarski(k2_tarski(esk3_0,k2_tops_1(esk2_0,esk3_0)))=k2_pre_topc(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_33]), c_0_82])).
% 0.19/0.45  cnf(c_0_94, negated_conjecture, (k2_pre_topc(esk2_0,esk3_0)=esk3_0|~v4_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_33]), c_0_34])])).
% 0.19/0.45  cnf(c_0_95, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_52]), c_0_39])).
% 0.19/0.45  cnf(c_0_96, negated_conjecture, (k3_subset_1(esk3_0,k1_tops_1(esk2_0,esk3_0))!=k2_tops_1(esk2_0,esk3_0)|~v4_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_75]), c_0_86])])).
% 0.19/0.45  cnf(c_0_97, negated_conjecture, (k3_subset_1(esk3_0,k1_tops_1(esk2_0,esk3_0))=k2_tops_1(esk2_0,esk3_0)|~r1_tarski(k2_tops_1(esk2_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.19/0.45  cnf(c_0_98, negated_conjecture, (v4_pre_topc(k2_pre_topc(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_33]), c_0_90]), c_0_34])])).
% 0.19/0.45  cnf(c_0_99, negated_conjecture, (k2_pre_topc(esk2_0,esk3_0)=esk3_0), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_80]), c_0_93]), c_0_94])).
% 0.19/0.45  cnf(c_0_100, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_95, c_0_72])).
% 0.19/0.45  cnf(c_0_101, negated_conjecture, (~v4_pre_topc(esk3_0,esk2_0)|~r1_tarski(k2_tops_1(esk2_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.19/0.45  cnf(c_0_102, negated_conjecture, (v4_pre_topc(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_98, c_0_99])).
% 0.19/0.45  cnf(c_0_103, negated_conjecture, (r1_tarski(k2_tops_1(esk2_0,esk3_0),k2_pre_topc(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_100, c_0_93])).
% 0.19/0.45  cnf(c_0_104, negated_conjecture, (~r1_tarski(k2_tops_1(esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_102])])).
% 0.19/0.45  cnf(c_0_105, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_99]), c_0_104]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 106
% 0.19/0.45  # Proof object clause steps            : 63
% 0.19/0.45  # Proof object formula steps           : 43
% 0.19/0.45  # Proof object conjectures             : 33
% 0.19/0.45  # Proof object clause conjectures      : 30
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 26
% 0.19/0.45  # Proof object initial formulas used   : 21
% 0.19/0.45  # Proof object generating inferences   : 23
% 0.19/0.45  # Proof object simplifying inferences  : 43
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 30
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 38
% 0.19/0.45  # Removed in clause preprocessing      : 5
% 0.19/0.45  # Initial clauses in saturation        : 33
% 0.19/0.45  # Processed clauses                    : 952
% 0.19/0.45  # ...of these trivial                  : 75
% 0.19/0.45  # ...subsumed                          : 351
% 0.19/0.45  # ...remaining for further processing  : 525
% 0.19/0.45  # Other redundant clauses eliminated   : 0
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 4
% 0.19/0.45  # Backward-rewritten                   : 101
% 0.19/0.45  # Generated clauses                    : 3918
% 0.19/0.45  # ...of the previous two non-trivial   : 2977
% 0.19/0.45  # Contextual simplify-reflections      : 1
% 0.19/0.45  # Paramodulations                      : 3918
% 0.19/0.45  # Factorizations                       : 0
% 0.19/0.45  # Equation resolutions                 : 0
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 387
% 0.19/0.45  #    Positive orientable unit clauses  : 164
% 0.19/0.45  #    Positive unorientable unit clauses: 1
% 0.19/0.45  #    Negative unit clauses             : 1
% 0.19/0.45  #    Non-unit-clauses                  : 221
% 0.19/0.45  # Current number of unprocessed clauses: 2059
% 0.19/0.45  # ...number of literals in the above   : 4430
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 143
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 7133
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 6293
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 355
% 0.19/0.45  # Unit Clause-clause subsumption calls : 633
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 448
% 0.19/0.45  # BW rewrite match successes           : 29
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 57901
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.107 s
% 0.19/0.45  # System time              : 0.008 s
% 0.19/0.45  # Total time               : 0.115 s
% 0.19/0.45  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
