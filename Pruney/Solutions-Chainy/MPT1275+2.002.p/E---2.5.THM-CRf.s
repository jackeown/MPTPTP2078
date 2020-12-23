%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:18 EST 2020

% Result     : Theorem 0.67s
% Output     : CNFRefutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 438 expanded)
%              Number of clauses        :   64 ( 181 expanded)
%              Number of leaves         :   20 ( 107 expanded)
%              Depth                    :   11
%              Number of atoms          :  254 (1346 expanded)
%              Number of equality atoms :   70 ( 348 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t94_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
           => ( v3_tops_1(X2,X1)
            <=> X2 = k2_tops_1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

fof(t92_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tops_1(X2,X1)
           => v2_tops_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t88_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> r1_tarski(X2,k2_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t93_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v2_tops_1(X2,X1)
              & v4_pre_topc(X2,X1) )
           => v3_tops_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_tops_1)).

fof(t84_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(d6_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

fof(t22_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).

fof(t53_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v3_pre_topc(X2,X1)
             => k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) )
             => v3_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_pre_topc)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => ( v3_tops_1(X2,X1)
              <=> X2 = k2_tops_1(X1,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t94_tops_1])).

fof(c_0_21,plain,(
    ! [X53,X54] :
      ( ~ l1_pre_topc(X53)
      | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))
      | ~ v3_tops_1(X54,X53)
      | v2_tops_1(X54,X53) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_tops_1])])])).

fof(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & v4_pre_topc(esk3_0,esk2_0)
    & ( ~ v3_tops_1(esk3_0,esk2_0)
      | esk3_0 != k2_tops_1(esk2_0,esk3_0) )
    & ( v3_tops_1(esk3_0,esk2_0)
      | esk3_0 = k2_tops_1(esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_23,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_24,plain,(
    ! [X34,X35] : k1_setfam_1(k2_tarski(X34,X35)) = k3_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_25,plain,(
    ! [X51,X52] :
      ( ( ~ v2_tops_1(X52,X51)
        | r1_tarski(X52,k2_tops_1(X51,X52))
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))
        | ~ l1_pre_topc(X51) )
      & ( ~ r1_tarski(X52,k2_tops_1(X51,X52))
        | v2_tops_1(X52,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))
        | ~ l1_pre_topc(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_tops_1])])])])).

cnf(c_0_26,plain,
    ( v2_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tops_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_30,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | k7_subset_1(X30,X31,X32) = k4_xboole_0(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X24] : m1_subset_1(k2_subset_1(X24),k1_zfmisc_1(X24)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_34,plain,(
    ! [X21] : k2_subset_1(X21) = X21 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_35,plain,(
    ! [X55,X56] :
      ( ~ l1_pre_topc(X55)
      | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
      | ~ v2_tops_1(X56,X55)
      | ~ v4_pre_topc(X56,X55)
      | v3_tops_1(X56,X55) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t93_tops_1])])])).

fof(c_0_36,plain,(
    ! [X49,X50] :
      ( ( ~ v2_tops_1(X50,X49)
        | k1_tops_1(X49,X50) = k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ l1_pre_topc(X49) )
      & ( k1_tops_1(X49,X50) != k1_xboole_0
        | v2_tops_1(X50,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ l1_pre_topc(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).

cnf(c_0_37,plain,
    ( v2_tops_1(X1,X2)
    | ~ r1_tarski(X1,k2_tops_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( v2_tops_1(esk3_0,esk2_0)
    | ~ v3_tops_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_39,negated_conjecture,
    ( v3_tops_1(esk3_0,esk2_0)
    | esk3_0 = k2_tops_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_41,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | k3_subset_1(X22,X23) = k4_xboole_0(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_42,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_44,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_46,plain,(
    ! [X42] :
      ( ~ l1_pre_topc(X42)
      | l1_struct_0(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_47,plain,
    ( v3_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tops_1(X2,X1)
    | ~ v4_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_49,plain,
    ( k1_tops_1(X2,X1) = k1_xboole_0
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( v2_tops_1(esk3_0,esk2_0)
    | ~ r1_tarski(esk3_0,k2_tops_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_27]),c_0_28])])).

cnf(c_0_51,negated_conjecture,
    ( k2_tops_1(esk2_0,esk3_0) = esk3_0
    | v2_tops_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_56,plain,(
    ! [X39] :
      ( ~ l1_struct_0(X39)
      | k2_struct_0(X39) = u1_struct_0(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_57,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k2_tops_1(X2,X1))
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_59,negated_conjecture,
    ( ~ v3_tops_1(esk3_0,esk2_0)
    | esk3_0 != k2_tops_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_60,negated_conjecture,
    ( v3_tops_1(esk3_0,esk2_0)
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_27]),c_0_48]),c_0_28])])).

fof(c_0_61,plain,(
    ! [X47,X48] :
      ( ~ l1_pre_topc(X47)
      | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
      | k2_tops_1(X47,X48) = k7_subset_1(u1_struct_0(X47),k2_pre_topc(X47,X48),k1_tops_1(X47,X48)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_62,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = k1_xboole_0
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_27]),c_0_28])])).

cnf(c_0_63,negated_conjecture,
    ( v2_tops_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_64,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_53,c_0_43])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_66,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_28])).

fof(c_0_68,plain,(
    ! [X40,X41] :
      ( ( ~ v4_pre_topc(X41,X40)
        | v3_pre_topc(k7_subset_1(u1_struct_0(X40),k2_struct_0(X40),X41),X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ l1_pre_topc(X40) )
      & ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X40),k2_struct_0(X40),X41),X40)
        | v4_pre_topc(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).

fof(c_0_69,plain,(
    ! [X43,X44] :
      ( ~ l1_struct_0(X43)
      | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
      | k7_subset_1(u1_struct_0(X43),k2_struct_0(X43),k7_subset_1(u1_struct_0(X43),k2_struct_0(X43),X44)) = X44 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk3_0,k2_tops_1(esk2_0,esk3_0))
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_27]),c_0_28])])).

cnf(c_0_71,negated_conjecture,
    ( k2_tops_1(esk2_0,esk3_0) != esk3_0
    | ~ v2_tops_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_72,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])])).

fof(c_0_74,plain,(
    ! [X45,X46] :
      ( ( ~ v3_pre_topc(X46,X45)
        | k2_pre_topc(X45,k7_subset_1(u1_struct_0(X45),k2_struct_0(X45),X46)) = k7_subset_1(u1_struct_0(X45),k2_struct_0(X45),X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_pre_topc(X45) )
      & ( ~ v2_pre_topc(X45)
        | k2_pre_topc(X45,k7_subset_1(u1_struct_0(X45),k2_struct_0(X45),X46)) != k7_subset_1(u1_struct_0(X45),k2_struct_0(X45),X46)
        | v3_pre_topc(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_pre_topc(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_pre_topc])])])])).

fof(c_0_75,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | m1_subset_1(k3_subset_1(X25,X26),k1_zfmisc_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_76,plain,
    ( k7_subset_1(X1,X1,X2) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_66]),c_0_67])])).

cnf(c_0_78,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_79,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_80,plain,(
    ! [X18] : k4_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_81,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(esk3_0,k2_tops_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_63])])).

cnf(c_0_83,negated_conjecture,
    ( k2_tops_1(esk2_0,esk3_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_63])])).

cnf(c_0_84,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),k1_xboole_0) = k2_tops_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_27]),c_0_28])]),c_0_73])).

cnf(c_0_85,plain,
    ( k2_pre_topc(X2,k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1)) = k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_86,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_87,negated_conjecture,
    ( k3_subset_1(k2_struct_0(esk2_0),esk3_0) = k7_subset_1(k2_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_88,negated_conjecture,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_27]),c_0_48]),c_0_28])])).

cnf(c_0_89,plain,
    ( k7_subset_1(k2_struct_0(X1),k2_struct_0(X1),k7_subset_1(k2_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_66])).

cnf(c_0_90,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k7_subset_1(u1_struct_0(esk2_0),esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_27])).

cnf(c_0_91,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_92,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])).

cnf(c_0_93,negated_conjecture,
    ( k2_tops_1(esk2_0,esk3_0) = k7_subset_1(k2_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_66]),c_0_67])])).

cnf(c_0_94,plain,
    ( k2_pre_topc(X1,k7_subset_1(k2_struct_0(X1),k2_struct_0(X1),X2)) = k7_subset_1(k2_struct_0(X1),k2_struct_0(X1),X2)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_66]),c_0_57])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(k7_subset_1(k2_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k2_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_77])])).

cnf(c_0_96,negated_conjecture,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_66]),c_0_67])])).

cnf(c_0_97,negated_conjecture,
    ( k7_subset_1(k2_struct_0(esk2_0),k2_struct_0(esk2_0),k7_subset_1(k2_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_77]),c_0_67])])).

cnf(c_0_98,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),esk3_0,X1) = k7_subset_1(esk3_0,esk3_0,X1) ),
    inference(rw,[status(thm)],[c_0_90,c_0_65])).

cnf(c_0_99,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_91,c_0_43])).

cnf(c_0_100,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(k2_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),k1_xboole_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_101,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96]),c_0_28])]),c_0_97]),c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( k7_subset_1(k2_struct_0(esk2_0),esk3_0,X1) = k7_subset_1(esk3_0,esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_66]),c_0_67])])).

cnf(c_0_103,plain,
    ( k7_subset_1(X1,X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_99,c_0_65])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_101]),c_0_102]),c_0_103]),c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:21:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.67/0.88  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.67/0.88  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.67/0.88  #
% 0.67/0.88  # Preprocessing time       : 0.029 s
% 0.67/0.88  # Presaturation interreduction done
% 0.67/0.88  
% 0.67/0.88  # Proof found!
% 0.67/0.88  # SZS status Theorem
% 0.67/0.88  # SZS output start CNFRefutation
% 0.67/0.88  fof(t94_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>(v3_tops_1(X2,X1)<=>X2=k2_tops_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 0.67/0.88  fof(t92_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)=>v2_tops_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 0.67/0.88  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.67/0.88  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.67/0.88  fof(t88_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>r1_tarski(X2,k2_tops_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 0.67/0.88  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.67/0.88  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.67/0.88  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.67/0.88  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.67/0.88  fof(t93_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tops_1(X2,X1)&v4_pre_topc(X2,X1))=>v3_tops_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_tops_1)).
% 0.67/0.88  fof(t84_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 0.67/0.88  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.67/0.88  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.67/0.88  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.67/0.88  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 0.67/0.88  fof(d6_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_pre_topc)).
% 0.67/0.88  fof(t22_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_pre_topc)).
% 0.67/0.88  fof(t53_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)=>k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))&((v2_pre_topc(X1)&k2_pre_topc(X1,k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=>v3_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_pre_topc)).
% 0.67/0.88  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.67/0.88  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.67/0.88  fof(c_0_20, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>(v3_tops_1(X2,X1)<=>X2=k2_tops_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t94_tops_1])).
% 0.67/0.88  fof(c_0_21, plain, ![X53, X54]:(~l1_pre_topc(X53)|(~m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))|(~v3_tops_1(X54,X53)|v2_tops_1(X54,X53)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_tops_1])])])).
% 0.67/0.88  fof(c_0_22, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(v4_pre_topc(esk3_0,esk2_0)&((~v3_tops_1(esk3_0,esk2_0)|esk3_0!=k2_tops_1(esk2_0,esk3_0))&(v3_tops_1(esk3_0,esk2_0)|esk3_0=k2_tops_1(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.67/0.88  fof(c_0_23, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.67/0.88  fof(c_0_24, plain, ![X34, X35]:k1_setfam_1(k2_tarski(X34,X35))=k3_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.67/0.88  fof(c_0_25, plain, ![X51, X52]:((~v2_tops_1(X52,X51)|r1_tarski(X52,k2_tops_1(X51,X52))|~m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))|~l1_pre_topc(X51))&(~r1_tarski(X52,k2_tops_1(X51,X52))|v2_tops_1(X52,X51)|~m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))|~l1_pre_topc(X51))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_tops_1])])])])).
% 0.67/0.88  cnf(c_0_26, plain, (v2_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_tops_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.67/0.88  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.67/0.88  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.67/0.88  fof(c_0_29, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.67/0.88  fof(c_0_30, plain, ![X30, X31, X32]:(~m1_subset_1(X31,k1_zfmisc_1(X30))|k7_subset_1(X30,X31,X32)=k4_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.67/0.88  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.67/0.88  cnf(c_0_32, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.67/0.88  fof(c_0_33, plain, ![X24]:m1_subset_1(k2_subset_1(X24),k1_zfmisc_1(X24)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.67/0.88  fof(c_0_34, plain, ![X21]:k2_subset_1(X21)=X21, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.67/0.88  fof(c_0_35, plain, ![X55, X56]:(~l1_pre_topc(X55)|(~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))|(~v2_tops_1(X56,X55)|~v4_pre_topc(X56,X55)|v3_tops_1(X56,X55)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t93_tops_1])])])).
% 0.67/0.88  fof(c_0_36, plain, ![X49, X50]:((~v2_tops_1(X50,X49)|k1_tops_1(X49,X50)=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))|~l1_pre_topc(X49))&(k1_tops_1(X49,X50)!=k1_xboole_0|v2_tops_1(X50,X49)|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))|~l1_pre_topc(X49))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).
% 0.67/0.88  cnf(c_0_37, plain, (v2_tops_1(X1,X2)|~r1_tarski(X1,k2_tops_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.67/0.88  cnf(c_0_38, negated_conjecture, (v2_tops_1(esk3_0,esk2_0)|~v3_tops_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.67/0.88  cnf(c_0_39, negated_conjecture, (v3_tops_1(esk3_0,esk2_0)|esk3_0=k2_tops_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.67/0.88  cnf(c_0_40, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.67/0.88  fof(c_0_41, plain, ![X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|k3_subset_1(X22,X23)=k4_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.67/0.88  cnf(c_0_42, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.67/0.88  cnf(c_0_43, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.67/0.88  cnf(c_0_44, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.67/0.88  cnf(c_0_45, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.67/0.88  fof(c_0_46, plain, ![X42]:(~l1_pre_topc(X42)|l1_struct_0(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.67/0.88  cnf(c_0_47, plain, (v3_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tops_1(X2,X1)|~v4_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.67/0.88  cnf(c_0_48, negated_conjecture, (v4_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.67/0.88  cnf(c_0_49, plain, (k1_tops_1(X2,X1)=k1_xboole_0|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.67/0.88  cnf(c_0_50, negated_conjecture, (v2_tops_1(esk3_0,esk2_0)|~r1_tarski(esk3_0,k2_tops_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_27]), c_0_28])])).
% 0.67/0.88  cnf(c_0_51, negated_conjecture, (k2_tops_1(esk2_0,esk3_0)=esk3_0|v2_tops_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.67/0.88  cnf(c_0_52, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_40])).
% 0.67/0.88  cnf(c_0_53, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.67/0.88  cnf(c_0_54, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.67/0.88  cnf(c_0_55, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.67/0.88  fof(c_0_56, plain, ![X39]:(~l1_struct_0(X39)|k2_struct_0(X39)=u1_struct_0(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.67/0.88  cnf(c_0_57, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.67/0.88  cnf(c_0_58, plain, (r1_tarski(X1,k2_tops_1(X2,X1))|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.67/0.88  cnf(c_0_59, negated_conjecture, (~v3_tops_1(esk3_0,esk2_0)|esk3_0!=k2_tops_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.67/0.88  cnf(c_0_60, negated_conjecture, (v3_tops_1(esk3_0,esk2_0)|~v2_tops_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_27]), c_0_48]), c_0_28])])).
% 0.67/0.88  fof(c_0_61, plain, ![X47, X48]:(~l1_pre_topc(X47)|(~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|k2_tops_1(X47,X48)=k7_subset_1(u1_struct_0(X47),k2_pre_topc(X47,X48),k1_tops_1(X47,X48)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 0.67/0.88  cnf(c_0_62, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=k1_xboole_0|~v2_tops_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_27]), c_0_28])])).
% 0.67/0.88  cnf(c_0_63, negated_conjecture, (v2_tops_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.67/0.88  cnf(c_0_64, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_53, c_0_43])).
% 0.67/0.88  cnf(c_0_65, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k7_subset_1(X1,X1,X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.67/0.88  cnf(c_0_66, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.67/0.88  cnf(c_0_67, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_57, c_0_28])).
% 0.67/0.88  fof(c_0_68, plain, ![X40, X41]:((~v4_pre_topc(X41,X40)|v3_pre_topc(k7_subset_1(u1_struct_0(X40),k2_struct_0(X40),X41),X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|~l1_pre_topc(X40))&(~v3_pre_topc(k7_subset_1(u1_struct_0(X40),k2_struct_0(X40),X41),X40)|v4_pre_topc(X41,X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|~l1_pre_topc(X40))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).
% 0.67/0.88  fof(c_0_69, plain, ![X43, X44]:(~l1_struct_0(X43)|(~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|k7_subset_1(u1_struct_0(X43),k2_struct_0(X43),k7_subset_1(u1_struct_0(X43),k2_struct_0(X43),X44))=X44)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).
% 0.67/0.88  cnf(c_0_70, negated_conjecture, (r1_tarski(esk3_0,k2_tops_1(esk2_0,esk3_0))|~v2_tops_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_27]), c_0_28])])).
% 0.67/0.88  cnf(c_0_71, negated_conjecture, (k2_tops_1(esk2_0,esk3_0)!=esk3_0|~v2_tops_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.67/0.88  cnf(c_0_72, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.67/0.88  cnf(c_0_73, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])])).
% 0.67/0.88  fof(c_0_74, plain, ![X45, X46]:((~v3_pre_topc(X46,X45)|k2_pre_topc(X45,k7_subset_1(u1_struct_0(X45),k2_struct_0(X45),X46))=k7_subset_1(u1_struct_0(X45),k2_struct_0(X45),X46)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_pre_topc(X45))&(~v2_pre_topc(X45)|k2_pre_topc(X45,k7_subset_1(u1_struct_0(X45),k2_struct_0(X45),X46))!=k7_subset_1(u1_struct_0(X45),k2_struct_0(X45),X46)|v3_pre_topc(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_pre_topc(X45))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_pre_topc])])])])).
% 0.67/0.88  fof(c_0_75, plain, ![X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(X25))|m1_subset_1(k3_subset_1(X25,X26),k1_zfmisc_1(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.67/0.88  cnf(c_0_76, plain, (k7_subset_1(X1,X1,X2)=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.67/0.88  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_66]), c_0_67])])).
% 0.67/0.88  cnf(c_0_78, plain, (v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.67/0.88  cnf(c_0_79, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.67/0.88  fof(c_0_80, plain, ![X18]:k4_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.67/0.88  cnf(c_0_81, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.67/0.88  cnf(c_0_82, negated_conjecture, (r1_tarski(esk3_0,k2_tops_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_63])])).
% 0.67/0.88  cnf(c_0_83, negated_conjecture, (k2_tops_1(esk2_0,esk3_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_63])])).
% 0.67/0.88  cnf(c_0_84, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),k1_xboole_0)=k2_tops_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_27]), c_0_28])]), c_0_73])).
% 0.67/0.88  cnf(c_0_85, plain, (k2_pre_topc(X2,k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1))=k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1)|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.67/0.88  cnf(c_0_86, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.67/0.88  cnf(c_0_87, negated_conjecture, (k3_subset_1(k2_struct_0(esk2_0),esk3_0)=k7_subset_1(k2_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.67/0.88  cnf(c_0_88, negated_conjecture, (v3_pre_topc(k7_subset_1(u1_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_27]), c_0_48]), c_0_28])])).
% 0.67/0.88  cnf(c_0_89, plain, (k7_subset_1(k2_struct_0(X1),k2_struct_0(X1),k7_subset_1(k2_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1)))), inference(spm,[status(thm)],[c_0_79, c_0_66])).
% 0.67/0.88  cnf(c_0_90, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k7_subset_1(u1_struct_0(esk2_0),esk3_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_27])).
% 0.67/0.88  cnf(c_0_91, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.67/0.88  cnf(c_0_92, negated_conjecture, (~r1_tarski(k2_tops_1(esk2_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])).
% 0.67/0.88  cnf(c_0_93, negated_conjecture, (k2_tops_1(esk2_0,esk3_0)=k7_subset_1(k2_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_66]), c_0_67])])).
% 0.67/0.88  cnf(c_0_94, plain, (k2_pre_topc(X1,k7_subset_1(k2_struct_0(X1),k2_struct_0(X1),X2))=k7_subset_1(k2_struct_0(X1),k2_struct_0(X1),X2)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_66]), c_0_57])).
% 0.67/0.88  cnf(c_0_95, negated_conjecture, (m1_subset_1(k7_subset_1(k2_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0),k1_zfmisc_1(k2_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_77])])).
% 0.67/0.88  cnf(c_0_96, negated_conjecture, (v3_pre_topc(k7_subset_1(k2_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_66]), c_0_67])])).
% 0.67/0.88  cnf(c_0_97, negated_conjecture, (k7_subset_1(k2_struct_0(esk2_0),k2_struct_0(esk2_0),k7_subset_1(k2_struct_0(esk2_0),k2_struct_0(esk2_0),esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_77]), c_0_67])])).
% 0.67/0.88  cnf(c_0_98, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),esk3_0,X1)=k7_subset_1(esk3_0,esk3_0,X1)), inference(rw,[status(thm)],[c_0_90, c_0_65])).
% 0.67/0.88  cnf(c_0_99, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_91, c_0_43])).
% 0.67/0.88  cnf(c_0_100, negated_conjecture, (~r1_tarski(k7_subset_1(k2_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),k1_xboole_0),esk3_0)), inference(rw,[status(thm)],[c_0_92, c_0_93])).
% 0.67/0.88  cnf(c_0_101, negated_conjecture, (k2_pre_topc(esk2_0,esk3_0)=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96]), c_0_28])]), c_0_97]), c_0_97])).
% 0.67/0.88  cnf(c_0_102, negated_conjecture, (k7_subset_1(k2_struct_0(esk2_0),esk3_0,X1)=k7_subset_1(esk3_0,esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_66]), c_0_67])])).
% 0.67/0.88  cnf(c_0_103, plain, (k7_subset_1(X1,X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_99, c_0_65])).
% 0.67/0.88  cnf(c_0_104, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_101]), c_0_102]), c_0_103]), c_0_52])]), ['proof']).
% 0.67/0.88  # SZS output end CNFRefutation
% 0.67/0.88  # Proof object total steps             : 105
% 0.67/0.88  # Proof object clause steps            : 64
% 0.67/0.88  # Proof object formula steps           : 41
% 0.67/0.88  # Proof object conjectures             : 35
% 0.67/0.88  # Proof object clause conjectures      : 32
% 0.67/0.88  # Proof object formula conjectures     : 3
% 0.67/0.88  # Proof object initial clauses used    : 26
% 0.67/0.88  # Proof object initial formulas used   : 20
% 0.67/0.88  # Proof object generating inferences   : 24
% 0.67/0.88  # Proof object simplifying inferences  : 59
% 0.67/0.88  # Training examples: 0 positive, 0 negative
% 0.67/0.88  # Parsed axioms                        : 25
% 0.67/0.88  # Removed by relevancy pruning/SinE    : 0
% 0.67/0.88  # Initial clauses                      : 40
% 0.67/0.88  # Removed in clause preprocessing      : 3
% 0.67/0.88  # Initial clauses in saturation        : 37
% 0.67/0.88  # Processed clauses                    : 4374
% 0.67/0.88  # ...of these trivial                  : 104
% 0.67/0.88  # ...subsumed                          : 3193
% 0.67/0.88  # ...remaining for further processing  : 1077
% 0.67/0.88  # Other redundant clauses eliminated   : 8
% 0.67/0.88  # Clauses deleted for lack of memory   : 0
% 0.67/0.88  # Backward-subsumed                    : 50
% 0.67/0.88  # Backward-rewritten                   : 104
% 0.67/0.88  # Generated clauses                    : 41077
% 0.67/0.88  # ...of the previous two non-trivial   : 38010
% 0.67/0.88  # Contextual simplify-reflections      : 23
% 0.67/0.88  # Paramodulations                      : 41015
% 0.67/0.88  # Factorizations                       : 44
% 0.67/0.88  # Equation resolutions                 : 17
% 0.67/0.88  # Propositional unsat checks           : 0
% 0.67/0.88  #    Propositional check models        : 0
% 0.67/0.88  #    Propositional check unsatisfiable : 0
% 0.67/0.88  #    Propositional clauses             : 0
% 0.67/0.88  #    Propositional clauses after purity: 0
% 0.67/0.88  #    Propositional unsat core size     : 0
% 0.67/0.88  #    Propositional preprocessing time  : 0.000
% 0.67/0.88  #    Propositional encoding time       : 0.000
% 0.67/0.88  #    Propositional solver time         : 0.000
% 0.67/0.88  #    Success case prop preproc time    : 0.000
% 0.67/0.88  #    Success case prop encoding time   : 0.000
% 0.67/0.88  #    Success case prop solver time     : 0.000
% 0.67/0.88  # Current number of processed clauses  : 884
% 0.67/0.88  #    Positive orientable unit clauses  : 80
% 0.67/0.88  #    Positive unorientable unit clauses: 7
% 0.67/0.88  #    Negative unit clauses             : 2
% 0.67/0.88  #    Non-unit-clauses                  : 795
% 0.67/0.88  # Current number of unprocessed clauses: 33234
% 0.67/0.88  # ...number of literals in the above   : 121810
% 0.67/0.88  # Current number of archived formulas  : 0
% 0.67/0.88  # Current number of archived clauses   : 194
% 0.67/0.88  # Clause-clause subsumption calls (NU) : 69076
% 0.67/0.88  # Rec. Clause-clause subsumption calls : 52104
% 0.67/0.88  # Non-unit clause-clause subsumptions  : 3066
% 0.67/0.88  # Unit Clause-clause subsumption calls : 2202
% 0.67/0.88  # Rewrite failures with RHS unbound    : 176
% 0.67/0.88  # BW rewrite match attempts            : 1785
% 0.67/0.88  # BW rewrite match successes           : 71
% 0.67/0.88  # Condensation attempts                : 0
% 0.67/0.88  # Condensation successes               : 0
% 0.67/0.88  # Termbank termtop insertions          : 926201
% 0.67/0.89  
% 0.67/0.89  # -------------------------------------------------
% 0.67/0.89  # User time                : 0.529 s
% 0.67/0.89  # System time              : 0.023 s
% 0.67/0.89  # Total time               : 0.551 s
% 0.67/0.89  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
