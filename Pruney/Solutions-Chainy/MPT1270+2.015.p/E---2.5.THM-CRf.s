%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:13 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 543 expanded)
%              Number of clauses        :   56 ( 220 expanded)
%              Number of leaves         :   20 ( 149 expanded)
%              Depth                    :   13
%              Number of atoms          :  232 (1115 expanded)
%              Number of equality atoms :   76 ( 439 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t88_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> r1_tarski(X2,k2_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

fof(t84_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(c_0_20,plain,(
    ! [X61,X62] : k1_setfam_1(k2_tarski(X61,X62)) = k3_xboole_0(X61,X62) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_21,plain,(
    ! [X31,X32] : k1_enumset1(X31,X31,X32) = k2_tarski(X31,X32) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X26,X27] : k4_xboole_0(X26,X27) = k5_xboole_0(X26,k3_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_23,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( r2_hidden(X17,X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X14)
        | r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X20)
        | X21 = k4_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k4_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X20)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k4_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_28,plain,(
    ! [X33,X34,X35] : k2_enumset1(X33,X33,X34,X35) = k1_enumset1(X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_29,plain,(
    ! [X36,X37,X38,X39] : k3_enumset1(X36,X36,X37,X38,X39) = k2_enumset1(X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_30,plain,(
    ! [X40,X41,X42,X43,X44] : k4_enumset1(X40,X40,X41,X42,X43,X44) = k3_enumset1(X40,X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_31,plain,(
    ! [X45,X46,X47,X48,X49,X50] : k5_enumset1(X45,X45,X46,X47,X48,X49,X50) = k4_enumset1(X45,X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_32,plain,(
    ! [X51,X52,X53,X54,X55,X56,X57] : k6_enumset1(X51,X51,X52,X53,X54,X55,X56,X57) = k5_enumset1(X51,X52,X53,X54,X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_40,plain,(
    ! [X58,X59,X60] :
      ( ~ m1_subset_1(X59,k1_zfmisc_1(X58))
      | k7_subset_1(X58,X59,X60) = k4_xboole_0(X59,X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_42,plain,(
    ! [X30] : k4_xboole_0(k1_xboole_0,X30) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_43,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v2_tops_1(X2,X1)
            <=> r1_tarski(X2,k2_tops_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t88_tops_1])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4)))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_45,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( X3 != k5_xboole_0(X4,k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_48,plain,(
    ! [X71,X72] :
      ( ( ~ v2_tops_1(X72,X71)
        | k1_tops_1(X71,X72) = k1_xboole_0
        | ~ m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(X71)))
        | ~ l1_pre_topc(X71) )
      & ( k1_tops_1(X71,X72) != k1_xboole_0
        | v2_tops_1(X72,X71)
        | ~ m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(X71)))
        | ~ l1_pre_topc(X71) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).

fof(c_0_49,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ( ~ v2_tops_1(esk5_0,esk4_0)
      | ~ r1_tarski(esk5_0,k2_tops_1(esk4_0,esk5_0)) )
    & ( v2_tops_1(esk5_0,esk4_0)
      | r1_tarski(esk5_0,k2_tops_1(esk4_0,esk5_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).

fof(c_0_50,plain,(
    ! [X29] : k4_xboole_0(X29,k1_xboole_0) = X29 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

fof(c_0_53,plain,(
    ! [X69,X70] :
      ( ~ l1_pre_topc(X69)
      | ~ m1_subset_1(X70,k1_zfmisc_1(u1_struct_0(X69)))
      | k1_tops_1(X69,X70) = k7_subset_1(u1_struct_0(X69),X70,k2_tops_1(X69,X70)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

fof(c_0_56,plain,(
    ! [X23,X24] :
      ( ( ~ r2_hidden(esk3_2(X23,X24),X23)
        | ~ r2_hidden(esk3_2(X23,X24),X24)
        | X23 = X24 )
      & ( r2_hidden(esk3_2(X23,X24),X23)
        | r2_hidden(esk3_2(X23,X24),X24)
        | X23 = X24 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_57,plain,(
    ! [X67,X68] :
      ( ~ l1_pre_topc(X67)
      | ~ m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))
      | k2_tops_1(X67,X68) = k7_subset_1(u1_struct_0(X67),k2_pre_topc(X67,X68),k1_tops_1(X67,X68)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_58,plain,
    ( k1_tops_1(X2,X1) = k1_xboole_0
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r2_hidden(X1,k7_subset_1(X3,X2,X4)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( k1_tops_1(esk4_0,esk5_0) = k1_xboole_0
    | ~ v2_tops_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r2_hidden(X1,k1_tops_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1)
    | ~ r2_hidden(esk3_2(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk4_0),k2_pre_topc(esk4_0,esk5_0),k1_xboole_0) = k2_tops_1(esk4_0,esk5_0)
    | ~ v2_tops_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_60]),c_0_59])])).

cnf(c_0_72,plain,
    ( k7_subset_1(X1,X2,k1_xboole_0) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_52])).

fof(c_0_73,plain,(
    ! [X63,X64] :
      ( ~ l1_pre_topc(X63)
      | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))
      | m1_subset_1(k2_pre_topc(X63,X64),k1_zfmisc_1(u1_struct_0(X63))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_74,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,k7_subset_1(X2,X1,X4))
    | ~ r2_hidden(X3,X4) ),
    inference(spm,[status(thm)],[c_0_54,c_0_52])).

fof(c_0_75,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k1_tops_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_59]),c_0_60])])).

cnf(c_0_77,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_65])).

fof(c_0_78,plain,(
    ! [X65,X66] :
      ( ~ l1_pre_topc(X65)
      | ~ m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))
      | r1_tarski(X66,k2_pre_topc(X65,X66)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_79,negated_conjecture,
    ( k2_pre_topc(esk4_0,esk5_0) = k2_tops_1(esk4_0,esk5_0)
    | ~ v2_tops_1(esk5_0,esk4_0)
    | ~ m1_subset_1(k2_pre_topc(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_80,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,k1_tops_1(X1,X2))
    | ~ r2_hidden(X3,k2_tops_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_63])).

cnf(c_0_82,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( k1_tops_1(esk4_0,esk5_0) = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,k1_tops_1(esk4_0,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_84,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( k2_pre_topc(esk4_0,esk5_0) = k2_tops_1(esk4_0,esk5_0)
    | ~ v2_tops_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_60]),c_0_59])])).

cnf(c_0_86,negated_conjecture,
    ( v2_tops_1(esk5_0,esk4_0)
    | r1_tarski(esk5_0,k2_tops_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_87,negated_conjecture,
    ( ~ r2_hidden(X1,k1_tops_1(esk4_0,esk5_0))
    | ~ r2_hidden(X1,k2_tops_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_59]),c_0_60])])).

cnf(c_0_88,plain,
    ( v2_tops_1(X2,X1)
    | k1_tops_1(X1,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_89,negated_conjecture,
    ( k1_tops_1(esk4_0,esk5_0) = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,k1_tops_1(esk4_0,esk5_0)),X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(esk5_0,k2_tops_1(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_60]),c_0_59])]),c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( k1_tops_1(esk4_0,esk5_0) = k1_xboole_0
    | ~ r2_hidden(esk3_2(k1_xboole_0,k1_tops_1(esk4_0,esk5_0)),k2_tops_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_77])).

cnf(c_0_92,negated_conjecture,
    ( ~ v2_tops_1(esk5_0,esk4_0)
    | ~ r1_tarski(esk5_0,k2_tops_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_93,negated_conjecture,
    ( v2_tops_1(esk5_0,esk4_0)
    | k1_tops_1(esk4_0,esk5_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_59]),c_0_60])])).

cnf(c_0_94,negated_conjecture,
    ( k1_tops_1(esk4_0,esk5_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( ~ v2_tops_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_90])])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94])]),c_0_95]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n005.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 19:42:17 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.17/0.31  # Version: 2.5pre002
% 0.17/0.31  # No SInE strategy applied
% 0.17/0.31  # Trying AutoSched0 for 299 seconds
% 0.17/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.17/0.36  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.17/0.36  #
% 0.17/0.36  # Preprocessing time       : 0.028 s
% 0.17/0.36  # Presaturation interreduction done
% 0.17/0.36  
% 0.17/0.36  # Proof found!
% 0.17/0.36  # SZS status Theorem
% 0.17/0.36  # SZS output start CNFRefutation
% 0.17/0.36  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.17/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.17/0.36  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.17/0.36  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.17/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.17/0.36  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.17/0.36  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.17/0.36  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.17/0.36  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.17/0.36  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.17/0.36  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.17/0.36  fof(t88_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>r1_tarski(X2,k2_tops_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 0.17/0.36  fof(t84_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 0.17/0.36  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.17/0.36  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 0.17/0.36  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 0.17/0.36  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 0.17/0.36  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.17/0.36  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.17/0.36  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 0.17/0.36  fof(c_0_20, plain, ![X61, X62]:k1_setfam_1(k2_tarski(X61,X62))=k3_xboole_0(X61,X62), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.17/0.36  fof(c_0_21, plain, ![X31, X32]:k1_enumset1(X31,X31,X32)=k2_tarski(X31,X32), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.17/0.36  fof(c_0_22, plain, ![X26, X27]:k4_xboole_0(X26,X27)=k5_xboole_0(X26,k3_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.17/0.36  cnf(c_0_23, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.36  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.17/0.36  fof(c_0_25, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:((((r2_hidden(X17,X14)|~r2_hidden(X17,X16)|X16!=k4_xboole_0(X14,X15))&(~r2_hidden(X17,X15)|~r2_hidden(X17,X16)|X16!=k4_xboole_0(X14,X15)))&(~r2_hidden(X18,X14)|r2_hidden(X18,X15)|r2_hidden(X18,X16)|X16!=k4_xboole_0(X14,X15)))&((~r2_hidden(esk2_3(X19,X20,X21),X21)|(~r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X20))|X21=k4_xboole_0(X19,X20))&((r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k4_xboole_0(X19,X20))&(~r2_hidden(esk2_3(X19,X20,X21),X20)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k4_xboole_0(X19,X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.17/0.36  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.17/0.36  cnf(c_0_27, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.17/0.36  fof(c_0_28, plain, ![X33, X34, X35]:k2_enumset1(X33,X33,X34,X35)=k1_enumset1(X33,X34,X35), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.17/0.36  fof(c_0_29, plain, ![X36, X37, X38, X39]:k3_enumset1(X36,X36,X37,X38,X39)=k2_enumset1(X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.17/0.36  fof(c_0_30, plain, ![X40, X41, X42, X43, X44]:k4_enumset1(X40,X40,X41,X42,X43,X44)=k3_enumset1(X40,X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.17/0.36  fof(c_0_31, plain, ![X45, X46, X47, X48, X49, X50]:k5_enumset1(X45,X45,X46,X47,X48,X49,X50)=k4_enumset1(X45,X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.17/0.36  fof(c_0_32, plain, ![X51, X52, X53, X54, X55, X56, X57]:k6_enumset1(X51,X51,X52,X53,X54,X55,X56,X57)=k5_enumset1(X51,X52,X53,X54,X55,X56,X57), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.17/0.36  cnf(c_0_33, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.36  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.17/0.36  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.17/0.36  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.17/0.36  cnf(c_0_37, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.17/0.36  cnf(c_0_38, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.17/0.36  cnf(c_0_39, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.17/0.36  fof(c_0_40, plain, ![X58, X59, X60]:(~m1_subset_1(X59,k1_zfmisc_1(X58))|k7_subset_1(X58,X59,X60)=k4_xboole_0(X59,X60)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.17/0.36  cnf(c_0_41, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.36  fof(c_0_42, plain, ![X30]:k4_xboole_0(k1_xboole_0,X30)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.17/0.36  fof(c_0_43, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>r1_tarski(X2,k2_tops_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t88_tops_1])).
% 0.17/0.36  cnf(c_0_44, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4)))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.17/0.36  cnf(c_0_45, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.17/0.36  cnf(c_0_46, plain, (X3!=k5_xboole_0(X4,k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.17/0.36  cnf(c_0_47, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.17/0.36  fof(c_0_48, plain, ![X71, X72]:((~v2_tops_1(X72,X71)|k1_tops_1(X71,X72)=k1_xboole_0|~m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(X71)))|~l1_pre_topc(X71))&(k1_tops_1(X71,X72)!=k1_xboole_0|v2_tops_1(X72,X71)|~m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(X71)))|~l1_pre_topc(X71))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).
% 0.17/0.36  fof(c_0_49, negated_conjecture, (l1_pre_topc(esk4_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&((~v2_tops_1(esk5_0,esk4_0)|~r1_tarski(esk5_0,k2_tops_1(esk4_0,esk5_0)))&(v2_tops_1(esk5_0,esk4_0)|r1_tarski(esk5_0,k2_tops_1(esk4_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).
% 0.17/0.36  fof(c_0_50, plain, ![X29]:k4_xboole_0(X29,k1_xboole_0)=X29, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.17/0.36  cnf(c_0_51, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))), inference(er,[status(thm)],[c_0_44])).
% 0.17/0.36  cnf(c_0_52, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.17/0.36  fof(c_0_53, plain, ![X69, X70]:(~l1_pre_topc(X69)|(~m1_subset_1(X70,k1_zfmisc_1(u1_struct_0(X69)))|k1_tops_1(X69,X70)=k7_subset_1(u1_struct_0(X69),X70,k2_tops_1(X69,X70)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 0.17/0.36  cnf(c_0_54, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_46])).
% 0.17/0.36  cnf(c_0_55, plain, (k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.17/0.36  fof(c_0_56, plain, ![X23, X24]:((~r2_hidden(esk3_2(X23,X24),X23)|~r2_hidden(esk3_2(X23,X24),X24)|X23=X24)&(r2_hidden(esk3_2(X23,X24),X23)|r2_hidden(esk3_2(X23,X24),X24)|X23=X24)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.17/0.36  fof(c_0_57, plain, ![X67, X68]:(~l1_pre_topc(X67)|(~m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))|k2_tops_1(X67,X68)=k7_subset_1(u1_struct_0(X67),k2_pre_topc(X67,X68),k1_tops_1(X67,X68)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 0.17/0.36  cnf(c_0_58, plain, (k1_tops_1(X2,X1)=k1_xboole_0|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.17/0.36  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.17/0.36  cnf(c_0_60, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.17/0.36  cnf(c_0_61, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.17/0.36  cnf(c_0_62, plain, (r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r2_hidden(X1,k7_subset_1(X3,X2,X4))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.17/0.36  cnf(c_0_63, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.17/0.36  cnf(c_0_64, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.17/0.36  cnf(c_0_65, plain, (r2_hidden(esk3_2(X1,X2),X1)|r2_hidden(esk3_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.17/0.36  cnf(c_0_66, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.17/0.36  cnf(c_0_67, negated_conjecture, (k1_tops_1(esk4_0,esk5_0)=k1_xboole_0|~v2_tops_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])])).
% 0.17/0.36  cnf(c_0_68, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.17/0.36  cnf(c_0_69, plain, (r2_hidden(X1,X2)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~r2_hidden(X1,k1_tops_1(X3,X2))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.17/0.36  cnf(c_0_70, plain, (k1_xboole_0=X1|r2_hidden(esk3_2(k1_xboole_0,X1),X1)|~r2_hidden(esk3_2(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.17/0.36  cnf(c_0_71, negated_conjecture, (k7_subset_1(u1_struct_0(esk4_0),k2_pre_topc(esk4_0,esk5_0),k1_xboole_0)=k2_tops_1(esk4_0,esk5_0)|~v2_tops_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_60]), c_0_59])])).
% 0.17/0.36  cnf(c_0_72, plain, (k7_subset_1(X1,X2,k1_xboole_0)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_68, c_0_52])).
% 0.17/0.36  fof(c_0_73, plain, ![X63, X64]:(~l1_pre_topc(X63)|~m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))|m1_subset_1(k2_pre_topc(X63,X64),k1_zfmisc_1(u1_struct_0(X63)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.17/0.36  cnf(c_0_74, plain, (~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,k7_subset_1(X2,X1,X4))|~r2_hidden(X3,X4)), inference(spm,[status(thm)],[c_0_54, c_0_52])).
% 0.17/0.36  fof(c_0_75, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.17/0.36  cnf(c_0_76, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k1_tops_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_59]), c_0_60])])).
% 0.17/0.36  cnf(c_0_77, plain, (k1_xboole_0=X1|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_70, c_0_65])).
% 0.17/0.36  fof(c_0_78, plain, ![X65, X66]:(~l1_pre_topc(X65)|(~m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))|r1_tarski(X66,k2_pre_topc(X65,X66)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 0.17/0.36  cnf(c_0_79, negated_conjecture, (k2_pre_topc(esk4_0,esk5_0)=k2_tops_1(esk4_0,esk5_0)|~v2_tops_1(esk5_0,esk4_0)|~m1_subset_1(k2_pre_topc(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.17/0.36  cnf(c_0_80, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.17/0.36  cnf(c_0_81, plain, (~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,k1_tops_1(X1,X2))|~r2_hidden(X3,k2_tops_1(X1,X2))), inference(spm,[status(thm)],[c_0_74, c_0_63])).
% 0.17/0.36  cnf(c_0_82, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.17/0.36  cnf(c_0_83, negated_conjecture, (k1_tops_1(esk4_0,esk5_0)=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,k1_tops_1(esk4_0,esk5_0)),esk5_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.17/0.36  cnf(c_0_84, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.17/0.36  cnf(c_0_85, negated_conjecture, (k2_pre_topc(esk4_0,esk5_0)=k2_tops_1(esk4_0,esk5_0)|~v2_tops_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_60]), c_0_59])])).
% 0.17/0.36  cnf(c_0_86, negated_conjecture, (v2_tops_1(esk5_0,esk4_0)|r1_tarski(esk5_0,k2_tops_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.17/0.36  cnf(c_0_87, negated_conjecture, (~r2_hidden(X1,k1_tops_1(esk4_0,esk5_0))|~r2_hidden(X1,k2_tops_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_59]), c_0_60])])).
% 0.17/0.36  cnf(c_0_88, plain, (v2_tops_1(X2,X1)|k1_tops_1(X1,X2)!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.17/0.36  cnf(c_0_89, negated_conjecture, (k1_tops_1(esk4_0,esk5_0)=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,k1_tops_1(esk4_0,esk5_0)),X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.17/0.36  cnf(c_0_90, negated_conjecture, (r1_tarski(esk5_0,k2_tops_1(esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_60]), c_0_59])]), c_0_86])).
% 0.17/0.36  cnf(c_0_91, negated_conjecture, (k1_tops_1(esk4_0,esk5_0)=k1_xboole_0|~r2_hidden(esk3_2(k1_xboole_0,k1_tops_1(esk4_0,esk5_0)),k2_tops_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_87, c_0_77])).
% 0.17/0.36  cnf(c_0_92, negated_conjecture, (~v2_tops_1(esk5_0,esk4_0)|~r1_tarski(esk5_0,k2_tops_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.17/0.36  cnf(c_0_93, negated_conjecture, (v2_tops_1(esk5_0,esk4_0)|k1_tops_1(esk4_0,esk5_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_59]), c_0_60])])).
% 0.17/0.36  cnf(c_0_94, negated_conjecture, (k1_tops_1(esk4_0,esk5_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91])).
% 0.17/0.36  cnf(c_0_95, negated_conjecture, (~v2_tops_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_90])])).
% 0.17/0.36  cnf(c_0_96, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_94])]), c_0_95]), ['proof']).
% 0.17/0.36  # SZS output end CNFRefutation
% 0.17/0.36  # Proof object total steps             : 97
% 0.17/0.36  # Proof object clause steps            : 56
% 0.17/0.36  # Proof object formula steps           : 41
% 0.17/0.36  # Proof object conjectures             : 21
% 0.17/0.36  # Proof object clause conjectures      : 18
% 0.17/0.36  # Proof object formula conjectures     : 3
% 0.17/0.36  # Proof object initial clauses used    : 25
% 0.17/0.36  # Proof object initial formulas used   : 20
% 0.17/0.36  # Proof object generating inferences   : 20
% 0.17/0.36  # Proof object simplifying inferences  : 58
% 0.17/0.36  # Training examples: 0 positive, 0 negative
% 0.17/0.36  # Parsed axioms                        : 21
% 0.17/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.36  # Initial clauses                      : 33
% 0.17/0.36  # Removed in clause preprocessing      : 8
% 0.17/0.36  # Initial clauses in saturation        : 25
% 0.17/0.36  # Processed clauses                    : 225
% 0.17/0.36  # ...of these trivial                  : 0
% 0.17/0.36  # ...subsumed                          : 79
% 0.17/0.36  # ...remaining for further processing  : 146
% 0.17/0.36  # Other redundant clauses eliminated   : 3
% 0.17/0.36  # Clauses deleted for lack of memory   : 0
% 0.17/0.36  # Backward-subsumed                    : 13
% 0.17/0.36  # Backward-rewritten                   : 14
% 0.17/0.36  # Generated clauses                    : 546
% 0.17/0.36  # ...of the previous two non-trivial   : 513
% 0.17/0.36  # Contextual simplify-reflections      : 7
% 0.17/0.36  # Paramodulations                      : 534
% 0.17/0.36  # Factorizations                       : 6
% 0.17/0.36  # Equation resolutions                 : 3
% 0.17/0.36  # Propositional unsat checks           : 0
% 0.17/0.36  #    Propositional check models        : 0
% 0.17/0.36  #    Propositional check unsatisfiable : 0
% 0.17/0.36  #    Propositional clauses             : 0
% 0.17/0.36  #    Propositional clauses after purity: 0
% 0.17/0.36  #    Propositional unsat core size     : 0
% 0.17/0.36  #    Propositional preprocessing time  : 0.000
% 0.17/0.36  #    Propositional encoding time       : 0.000
% 0.17/0.36  #    Propositional solver time         : 0.000
% 0.17/0.36  #    Success case prop preproc time    : 0.000
% 0.17/0.36  #    Success case prop encoding time   : 0.000
% 0.17/0.36  #    Success case prop solver time     : 0.000
% 0.17/0.36  # Current number of processed clauses  : 88
% 0.17/0.36  #    Positive orientable unit clauses  : 9
% 0.17/0.36  #    Positive unorientable unit clauses: 0
% 0.17/0.36  #    Negative unit clauses             : 1
% 0.17/0.36  #    Non-unit-clauses                  : 78
% 0.17/0.36  # Current number of unprocessed clauses: 336
% 0.17/0.36  # ...number of literals in the above   : 1431
% 0.17/0.36  # Current number of archived formulas  : 0
% 0.17/0.36  # Current number of archived clauses   : 63
% 0.17/0.36  # Clause-clause subsumption calls (NU) : 1931
% 0.17/0.36  # Rec. Clause-clause subsumption calls : 961
% 0.17/0.36  # Non-unit clause-clause subsumptions  : 71
% 0.17/0.36  # Unit Clause-clause subsumption calls : 50
% 0.17/0.36  # Rewrite failures with RHS unbound    : 0
% 0.17/0.36  # BW rewrite match attempts            : 10
% 0.17/0.36  # BW rewrite match successes           : 2
% 0.17/0.36  # Condensation attempts                : 0
% 0.17/0.36  # Condensation successes               : 0
% 0.17/0.36  # Termbank termtop insertions          : 13554
% 0.17/0.36  
% 0.17/0.36  # -------------------------------------------------
% 0.17/0.36  # User time                : 0.047 s
% 0.17/0.36  # System time              : 0.005 s
% 0.17/0.36  # Total time               : 0.053 s
% 0.17/0.36  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
