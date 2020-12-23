%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:07 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 131 expanded)
%              Number of clauses        :   40 (  54 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  157 ( 331 expanded)
%              Number of equality atoms :   32 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t69_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
           => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

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

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t69_tops_1])).

fof(c_0_15,plain,(
    ! [X52,X53] :
      ( ( ~ m1_subset_1(X52,k1_zfmisc_1(X53))
        | r1_tarski(X52,X53) )
      & ( ~ r1_tarski(X52,X53)
        | m1_subset_1(X52,k1_zfmisc_1(X53)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_16,plain,(
    ! [X58,X59] :
      ( ~ l1_pre_topc(X58)
      | ~ m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))
      | m1_subset_1(k2_tops_1(X58,X59),k1_zfmisc_1(u1_struct_0(X58))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

fof(c_0_17,plain,(
    ! [X60,X61] :
      ( ~ l1_pre_topc(X60)
      | ~ m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))
      | k2_tops_1(X60,X61) = k2_tops_1(X60,k3_subset_1(u1_struct_0(X60),X61)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

fof(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & v4_pre_topc(esk3_0,esk2_0)
    & ~ r1_tarski(k2_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_19,plain,(
    ! [X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X39))
      | m1_subset_1(k3_subset_1(X39,X40),k1_zfmisc_1(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X45,X46,X47] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(X45))
      | ~ m1_subset_1(X47,k1_zfmisc_1(X45))
      | k4_subset_1(X45,X46,X47) = k2_xboole_0(X46,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_27,plain,(
    ! [X35,X36] : k3_tarski(k2_tarski(X35,X36)) = k2_xboole_0(X35,X36) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_28,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(k2_xboole_0(X12,X13),X14)
      | r1_tarski(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_29,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k2_xboole_0(X15,X16) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(k2_tops_1(X1,X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( k2_tops_1(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0)) = k2_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_25])).

cnf(c_0_33,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X33,X34] : k2_tarski(X33,X34) = k2_tarski(X34,X33) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk2_0,esk3_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_24])])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_23])).

fof(c_0_41,plain,(
    ! [X56,X57] :
      ( ( ~ v4_pre_topc(X57,X56)
        | k2_pre_topc(X56,X57) = X57
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
        | ~ l1_pre_topc(X56) )
      & ( ~ v2_pre_topc(X56)
        | k2_pre_topc(X56,X57) != X57
        | v4_pre_topc(X57,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
        | ~ l1_pre_topc(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

fof(c_0_42,plain,(
    ! [X31,X32] : r1_tarski(X31,k2_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_43,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_tarski(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3) ),
    inference(rw,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_45,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk2_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

fof(c_0_48,plain,(
    ! [X62,X63] :
      ( ~ l1_pre_topc(X62)
      | ~ m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))
      | k2_pre_topc(X62,X63) = k4_subset_1(u1_struct_0(X62),X63,k2_tops_1(X62,X63)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

cnf(c_0_49,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_51,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( k4_subset_1(X1,X2,X3) = k3_tarski(k2_tarski(X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_39])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k3_tarski(k2_tarski(X3,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( k3_tarski(k2_tarski(u1_struct_0(esk2_0),k2_tops_1(esk2_0,esk3_0))) = u1_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_45])).

cnf(c_0_56,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_23]),c_0_50]),c_0_24])])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_52,c_0_34])).

cnf(c_0_61,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk2_0),esk3_0,X1) = k3_tarski(k2_tarski(esk3_0,X1))
    | ~ r1_tarski(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_23])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk2_0,esk3_0),X1)
    | ~ r1_tarski(u1_struct_0(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk2_0),esk3_0,k2_tops_1(esk2_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_23]),c_0_24])]),c_0_57])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_45])).

cnf(c_0_66,negated_conjecture,
    ( k3_tarski(k2_tarski(esk3_0,k2_tops_1(esk2_0,esk3_0))) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64])])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.45  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.20/0.45  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.45  #
% 0.20/0.45  # Preprocessing time       : 0.041 s
% 0.20/0.45  # Presaturation interreduction done
% 0.20/0.45  
% 0.20/0.45  # Proof found!
% 0.20/0.45  # SZS status Theorem
% 0.20/0.45  # SZS output start CNFRefutation
% 0.20/0.45  fof(t69_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 0.20/0.45  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.45  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 0.20/0.45  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 0.20/0.45  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.20/0.45  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.20/0.45  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.45  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.20/0.45  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.45  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.20/0.45  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.20/0.45  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.45  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 0.20/0.45  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.45  fof(c_0_14, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t69_tops_1])).
% 0.20/0.45  fof(c_0_15, plain, ![X52, X53]:((~m1_subset_1(X52,k1_zfmisc_1(X53))|r1_tarski(X52,X53))&(~r1_tarski(X52,X53)|m1_subset_1(X52,k1_zfmisc_1(X53)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.45  fof(c_0_16, plain, ![X58, X59]:(~l1_pre_topc(X58)|~m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))|m1_subset_1(k2_tops_1(X58,X59),k1_zfmisc_1(u1_struct_0(X58)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 0.20/0.45  fof(c_0_17, plain, ![X60, X61]:(~l1_pre_topc(X60)|(~m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))|k2_tops_1(X60,X61)=k2_tops_1(X60,k3_subset_1(u1_struct_0(X60),X61)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 0.20/0.45  fof(c_0_18, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(v4_pre_topc(esk3_0,esk2_0)&~r1_tarski(k2_tops_1(esk2_0,esk3_0),esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.20/0.45  fof(c_0_19, plain, ![X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(X39))|m1_subset_1(k3_subset_1(X39,X40),k1_zfmisc_1(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.20/0.45  cnf(c_0_20, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.45  cnf(c_0_21, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.45  cnf(c_0_22, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.45  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.45  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.45  cnf(c_0_25, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  fof(c_0_26, plain, ![X45, X46, X47]:(~m1_subset_1(X46,k1_zfmisc_1(X45))|~m1_subset_1(X47,k1_zfmisc_1(X45))|k4_subset_1(X45,X46,X47)=k2_xboole_0(X46,X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.20/0.45  fof(c_0_27, plain, ![X35, X36]:k3_tarski(k2_tarski(X35,X36))=k2_xboole_0(X35,X36), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.45  fof(c_0_28, plain, ![X12, X13, X14]:(~r1_tarski(k2_xboole_0(X12,X13),X14)|r1_tarski(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.20/0.45  fof(c_0_29, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k2_xboole_0(X15,X16)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.45  cnf(c_0_30, plain, (r1_tarski(k2_tops_1(X1,X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.45  cnf(c_0_31, negated_conjecture, (k2_tops_1(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0))=k2_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.20/0.45  cnf(c_0_32, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_20, c_0_25])).
% 0.20/0.45  cnf(c_0_33, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.45  cnf(c_0_34, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.45  cnf(c_0_35, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.45  fof(c_0_36, plain, ![X33, X34]:k2_tarski(X33,X34)=k2_tarski(X34,X33), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.20/0.45  cnf(c_0_37, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.45  cnf(c_0_38, negated_conjecture, (r1_tarski(k2_tops_1(esk2_0,esk3_0),u1_struct_0(esk2_0))|~m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_24])])).
% 0.20/0.45  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.45  cnf(c_0_40, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_32, c_0_23])).
% 0.20/0.45  fof(c_0_41, plain, ![X56, X57]:((~v4_pre_topc(X57,X56)|k2_pre_topc(X56,X57)=X57|~m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))|~l1_pre_topc(X56))&(~v2_pre_topc(X56)|k2_pre_topc(X56,X57)!=X57|v4_pre_topc(X57,X56)|~m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))|~l1_pre_topc(X56))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.20/0.45  fof(c_0_42, plain, ![X31, X32]:r1_tarski(X31,k2_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.45  cnf(c_0_43, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_tarski(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.45  cnf(c_0_44, plain, (r1_tarski(X1,X3)|~r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3)), inference(rw,[status(thm)],[c_0_35, c_0_34])).
% 0.20/0.45  cnf(c_0_45, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.45  cnf(c_0_46, plain, (k3_tarski(k2_tarski(X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_37, c_0_34])).
% 0.20/0.45  cnf(c_0_47, negated_conjecture, (r1_tarski(k2_tops_1(esk2_0,esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.20/0.45  fof(c_0_48, plain, ![X62, X63]:(~l1_pre_topc(X62)|(~m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))|k2_pre_topc(X62,X63)=k4_subset_1(u1_struct_0(X62),X63,k2_tops_1(X62,X63)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 0.20/0.45  cnf(c_0_49, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.45  cnf(c_0_50, negated_conjecture, (v4_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.45  fof(c_0_51, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.45  cnf(c_0_52, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.45  cnf(c_0_53, plain, (k4_subset_1(X1,X2,X3)=k3_tarski(k2_tarski(X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_43, c_0_39])).
% 0.20/0.45  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~r1_tarski(k3_tarski(k2_tarski(X3,X1)),X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.45  cnf(c_0_55, negated_conjecture, (k3_tarski(k2_tarski(u1_struct_0(esk2_0),k2_tops_1(esk2_0,esk3_0)))=u1_struct_0(esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_45])).
% 0.20/0.45  cnf(c_0_56, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.45  cnf(c_0_57, negated_conjecture, (k2_pre_topc(esk2_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_23]), c_0_50]), c_0_24])])).
% 0.20/0.45  cnf(c_0_58, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.45  cnf(c_0_59, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.45  cnf(c_0_60, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_52, c_0_34])).
% 0.20/0.45  cnf(c_0_61, negated_conjecture, (k4_subset_1(u1_struct_0(esk2_0),esk3_0,X1)=k3_tarski(k2_tarski(esk3_0,X1))|~r1_tarski(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_53, c_0_23])).
% 0.20/0.45  cnf(c_0_62, negated_conjecture, (r1_tarski(k2_tops_1(esk2_0,esk3_0),X1)|~r1_tarski(u1_struct_0(esk2_0),X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.45  cnf(c_0_63, negated_conjecture, (k4_subset_1(u1_struct_0(esk2_0),esk3_0,k2_tops_1(esk2_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_23]), c_0_24])]), c_0_57])).
% 0.20/0.45  cnf(c_0_64, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.45  cnf(c_0_65, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_60, c_0_45])).
% 0.20/0.45  cnf(c_0_66, negated_conjecture, (k3_tarski(k2_tarski(esk3_0,k2_tops_1(esk2_0,esk3_0)))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64])])).
% 0.20/0.45  cnf(c_0_67, negated_conjecture, (~r1_tarski(k2_tops_1(esk2_0,esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.45  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), ['proof']).
% 0.20/0.45  # SZS output end CNFRefutation
% 0.20/0.45  # Proof object total steps             : 69
% 0.20/0.45  # Proof object clause steps            : 40
% 0.20/0.45  # Proof object formula steps           : 29
% 0.20/0.45  # Proof object conjectures             : 18
% 0.20/0.45  # Proof object clause conjectures      : 15
% 0.20/0.45  # Proof object formula conjectures     : 3
% 0.20/0.45  # Proof object initial clauses used    : 19
% 0.20/0.45  # Proof object initial formulas used   : 14
% 0.20/0.45  # Proof object generating inferences   : 17
% 0.20/0.45  # Proof object simplifying inferences  : 21
% 0.20/0.45  # Training examples: 0 positive, 0 negative
% 0.20/0.45  # Parsed axioms                        : 28
% 0.20/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.45  # Initial clauses                      : 35
% 0.20/0.45  # Removed in clause preprocessing      : 4
% 0.20/0.45  # Initial clauses in saturation        : 31
% 0.20/0.45  # Processed clauses                    : 592
% 0.20/0.45  # ...of these trivial                  : 52
% 0.20/0.45  # ...subsumed                          : 224
% 0.20/0.45  # ...remaining for further processing  : 316
% 0.20/0.45  # Other redundant clauses eliminated   : 0
% 0.20/0.45  # Clauses deleted for lack of memory   : 0
% 0.20/0.45  # Backward-subsumed                    : 0
% 0.20/0.45  # Backward-rewritten                   : 34
% 0.20/0.45  # Generated clauses                    : 2297
% 0.20/0.45  # ...of the previous two non-trivial   : 1691
% 0.20/0.45  # Contextual simplify-reflections      : 0
% 0.20/0.45  # Paramodulations                      : 2297
% 0.20/0.45  # Factorizations                       : 0
% 0.20/0.45  # Equation resolutions                 : 0
% 0.20/0.45  # Propositional unsat checks           : 0
% 0.20/0.45  #    Propositional check models        : 0
% 0.20/0.45  #    Propositional check unsatisfiable : 0
% 0.20/0.45  #    Propositional clauses             : 0
% 0.20/0.45  #    Propositional clauses after purity: 0
% 0.20/0.45  #    Propositional unsat core size     : 0
% 0.20/0.45  #    Propositional preprocessing time  : 0.000
% 0.20/0.45  #    Propositional encoding time       : 0.000
% 0.20/0.45  #    Propositional solver time         : 0.000
% 0.20/0.45  #    Success case prop preproc time    : 0.000
% 0.20/0.45  #    Success case prop encoding time   : 0.000
% 0.20/0.45  #    Success case prop solver time     : 0.000
% 0.20/0.45  # Current number of processed clauses  : 251
% 0.20/0.45  #    Positive orientable unit clauses  : 86
% 0.20/0.45  #    Positive unorientable unit clauses: 1
% 0.20/0.45  #    Negative unit clauses             : 21
% 0.20/0.45  #    Non-unit-clauses                  : 143
% 0.20/0.45  # Current number of unprocessed clauses: 1123
% 0.20/0.45  # ...number of literals in the above   : 2195
% 0.20/0.45  # Current number of archived formulas  : 0
% 0.20/0.45  # Current number of archived clauses   : 69
% 0.20/0.45  # Clause-clause subsumption calls (NU) : 1866
% 0.20/0.45  # Rec. Clause-clause subsumption calls : 1367
% 0.20/0.45  # Non-unit clause-clause subsumptions  : 72
% 0.20/0.45  # Unit Clause-clause subsumption calls : 1163
% 0.20/0.45  # Rewrite failures with RHS unbound    : 0
% 0.20/0.45  # BW rewrite match attempts            : 166
% 0.20/0.45  # BW rewrite match successes           : 25
% 0.20/0.45  # Condensation attempts                : 0
% 0.20/0.45  # Condensation successes               : 0
% 0.20/0.45  # Termbank termtop insertions          : 33153
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.101 s
% 0.20/0.45  # System time              : 0.007 s
% 0.20/0.45  # Total time               : 0.108 s
% 0.20/0.45  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
