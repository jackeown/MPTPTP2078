%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:17 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  164 (1820 expanded)
%              Number of clauses        :  109 ( 846 expanded)
%              Number of leaves         :   27 ( 468 expanded)
%              Depth                    :   16
%              Number of atoms          :  338 (3521 expanded)
%              Number of equality atoms :  112 (1617 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

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

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(t56_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X2,X1)
                  & r1_tarski(X2,X3) )
               => r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(c_0_27,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_28,plain,(
    ! [X57,X58] : k1_setfam_1(k2_tarski(X57,X58)) = k3_xboole_0(X57,X58) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_29,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_34,plain,(
    ! [X37,X38] : m1_subset_1(k6_subset_1(X37,X38),k1_zfmisc_1(X37)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_35,plain,(
    ! [X49,X50] : k6_subset_1(X49,X50) = k4_xboole_0(X49,X50) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_36,plain,(
    ! [X22] : k4_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_37,plain,(
    ! [X51,X52,X53] :
      ( ~ m1_subset_1(X52,k1_zfmisc_1(X51))
      | k7_subset_1(X51,X52,X53) = k4_xboole_0(X52,X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_38,plain,
    ( X3 != k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_39,plain,(
    ! [X29,X30] : k2_tarski(X29,X30) = k2_tarski(X30,X29) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_40,plain,(
    ! [X26] : k4_xboole_0(k1_xboole_0,X26) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_41,plain,(
    ! [X18,X19] : r1_tarski(k3_xboole_0(X18,X19),X18) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_42,plain,(
    ! [X59,X60] :
      ( ( ~ m1_subset_1(X59,k1_zfmisc_1(X60))
        | r1_tarski(X59,X60) )
      & ( ~ r1_tarski(X59,X60)
        | m1_subset_1(X59,k1_zfmisc_1(X60)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_43,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | m1_subset_1(k3_subset_1(X35,X36),k1_zfmisc_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_44,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_48,plain,(
    ! [X61,X62] :
      ( ~ l1_pre_topc(X61)
      | ~ m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))
      | m1_subset_1(k2_pre_topc(X61,X62),k1_zfmisc_1(u1_struct_0(X61))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_49,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

fof(c_0_50,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(X44))
      | ~ r2_hidden(X46,X45)
      | r2_hidden(X46,X44) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_55,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | k3_subset_1(X33,X34) = k4_xboole_0(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_33])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_46,c_0_33])).

cnf(c_0_60,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_47,c_0_33])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_62,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_63,negated_conjecture,
    ( v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( ~ v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) )
    & ( v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_49])])])).

cnf(c_0_64,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2))))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_53,c_0_33])).

cnf(c_0_67,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_54,c_0_31])).

fof(c_0_69,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k3_xboole_0(X24,X25)) = k4_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_70,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_71,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_72,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

fof(c_0_73,plain,(
    ! [X20,X21] : k2_xboole_0(X20,k3_xboole_0(X20,X21)) = X20 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_74,plain,(
    ! [X31,X32] : k3_tarski(k2_tarski(X31,X32)) = k2_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_75,plain,(
    ! [X23] :
      ( ~ r1_tarski(X23,k1_xboole_0)
      | X23 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_76,plain,(
    ! [X27,X28] : k2_xboole_0(X27,X28) = k5_xboole_0(X27,k4_xboole_0(X28,X27)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_77,plain,(
    ! [X74,X75] :
      ( ~ l1_pre_topc(X74)
      | ~ m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(X74)))
      | k1_tops_1(X74,X75) = k7_subset_1(u1_struct_0(X74),X75,k2_tops_1(X74,X75)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_78,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_79,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_62])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_81,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_64,c_0_61])).

cnf(c_0_83,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_84,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_67,c_0_33])).

cnf(c_0_85,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_52])).

cnf(c_0_86,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_87,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_70,c_0_33])).

cnf(c_0_88,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_89,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_90,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_91,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

fof(c_0_92,plain,(
    ! [X63,X64] :
      ( ~ l1_pre_topc(X63)
      | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))
      | r1_tarski(X64,k2_pre_topc(X63,X64)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_93,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_94,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_95,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,k7_subset_1(X2,X1,X4))
    | ~ r2_hidden(X3,X4) ),
    inference(spm,[status(thm)],[c_0_51,c_0_78])).

cnf(c_0_96,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk3_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])])).

cnf(c_0_98,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_68])).

cnf(c_0_99,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_66])).

cnf(c_0_100,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_85])).

cnf(c_0_101,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2))))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_31]),c_0_33]),c_0_33])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_61])).

cnf(c_0_103,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1))) = k3_subset_1(X1,X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_72])).

cnf(c_0_104,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_subset_1(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_88])).

cnf(c_0_105,plain,
    ( k3_tarski(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90]),c_0_31])).

cnf(c_0_106,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_85])).

cnf(c_0_107,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

fof(c_0_108,plain,(
    ! [X69,X70,X71] :
      ( ~ l1_pre_topc(X69)
      | ~ m1_subset_1(X70,k1_zfmisc_1(u1_struct_0(X69)))
      | ~ m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X69)))
      | ~ v3_pre_topc(X70,X69)
      | ~ r1_tarski(X70,X71)
      | r1_tarski(X70,k1_tops_1(X69,X71)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_109,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_90]),c_0_33])).

cnf(c_0_110,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0)) = k1_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_80]),c_0_81])])).

cnf(c_0_111,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1) = k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_80])).

cnf(c_0_112,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,k2_tops_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97])])).

cnf(c_0_113,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X3,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_114,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4)))
    | r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_tarski(X1,X2))),X3)
    | r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_tarski(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_100,c_0_84])).

cnf(c_0_115,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_68])])).

cnf(c_0_116,plain,
    ( ~ r2_hidden(X1,k3_subset_1(X2,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_103]),c_0_104])).

cnf(c_0_117,plain,
    ( k3_tarski(k2_tarski(X1,k1_xboole_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_118,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_119,negated_conjecture,
    ( r1_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_80]),c_0_81])])).

cnf(c_0_120,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_121,plain,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_101]),c_0_52]),c_0_105])).

cnf(c_0_122,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0)))) = k1_tops_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_123,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k2_tops_1(esk3_0,esk4_0),X1)) = k1_xboole_0
    | v3_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(esk1_3(k1_xboole_0,X2,k1_setfam_1(k2_tarski(k2_tops_1(esk3_0,esk4_0),X1))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_124,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_subset_1(X3,k1_setfam_1(k2_tarski(X3,X4)))
    | r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_tarski(X1,X2))),X2)
    | r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_tarski(X1,X2))),X3) ),
    inference(rw,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_125,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_68])).

cnf(c_0_126,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_116,c_0_99])).

cnf(c_0_127,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2)))) = k3_tarski(k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_52])).

cnf(c_0_128,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_59,c_0_106])).

cnf(c_0_129,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_117,c_0_52])).

fof(c_0_130,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_131,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_58])).

cnf(c_0_132,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_118,c_0_33])).

cnf(c_0_133,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_119])).

cnf(c_0_134,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_80]),c_0_81])])).

cnf(c_0_135,negated_conjecture,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0))),k1_tops_1(esk3_0,esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_136,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0))) = k1_xboole_0
    | v3_pre_topc(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_52]),c_0_52]),c_0_125]),c_0_126]),c_0_52])]),c_0_83])).

cnf(c_0_137,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_125]),c_0_128]),c_0_129])).

cnf(c_0_138,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_130])).

cnf(c_0_139,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_130])).

cnf(c_0_140,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_131,c_0_122])).

cnf(c_0_141,negated_conjecture,
    ( X1 = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k2_pre_topc(esk3_0,esk4_0))))
    | r2_hidden(esk1_3(X2,k2_pre_topc(esk3_0,esk4_0),X1),X1)
    | ~ r2_hidden(esk1_3(X2,k2_pre_topc(esk3_0,esk4_0),X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_132,c_0_133])).

cnf(c_0_142,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

fof(c_0_143,plain,(
    ! [X65,X66] :
      ( ~ v2_pre_topc(X65)
      | ~ l1_pre_topc(X65)
      | ~ m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))
      | v3_pre_topc(k1_tops_1(X65,X66),X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

fof(c_0_144,plain,(
    ! [X67,X68] :
      ( ~ l1_pre_topc(X67)
      | ~ m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))
      | k2_tops_1(X67,X68) = k7_subset_1(u1_struct_0(X67),k2_pre_topc(X67,X68),k1_tops_1(X67,X68)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_145,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_134,c_0_61])).

cnf(c_0_146,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0
    | v3_pre_topc(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_137])).

cnf(c_0_147,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_80])).

cnf(c_0_148,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_138])).

cnf(c_0_149,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0
    | ~ r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_140])).

cnf(c_0_150,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0)))) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_142]),c_0_83])).

cnf(c_0_151,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_143])).

cnf(c_0_152,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_153,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_144])).

cnf(c_0_154,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_146]),c_0_147]),c_0_148])]),c_0_149])).

cnf(c_0_155,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_156,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[c_0_78,c_0_115])).

cnf(c_0_157,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0))) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_150]),c_0_128])).

cnf(c_0_158,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_80]),c_0_152]),c_0_81])])).

cnf(c_0_159,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) = k2_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_154]),c_0_81]),c_0_80])])).

cnf(c_0_160,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0) != k2_tops_1(esk3_0,esk4_0)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_156]),c_0_52]),c_0_157]),c_0_97])])).

cnf(c_0_161,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_158,c_0_154])).

cnf(c_0_162,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0) = k2_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_159]),c_0_52]),c_0_157]),c_0_97])])).

cnf(c_0_163,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_160,c_0_161])]),c_0_162])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.74/2.91  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 2.74/2.91  # and selection function SelectMaxLComplexAvoidPosPred.
% 2.74/2.91  #
% 2.74/2.91  # Preprocessing time       : 0.029 s
% 2.74/2.91  # Presaturation interreduction done
% 2.74/2.91  
% 2.74/2.91  # Proof found!
% 2.74/2.91  # SZS status Theorem
% 2.74/2.91  # SZS output start CNFRefutation
% 2.74/2.91  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.74/2.91  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.74/2.91  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.74/2.91  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 2.74/2.91  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.74/2.91  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.74/2.91  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.74/2.91  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.74/2.91  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.74/2.91  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.74/2.91  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.74/2.91  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.74/2.91  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.74/2.91  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 2.74/2.91  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.74/2.91  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.74/2.91  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.74/2.91  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.74/2.91  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.74/2.91  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.74/2.91  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.74/2.91  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 2.74/2.91  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.74/2.91  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 2.74/2.91  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.74/2.91  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.74/2.91  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 2.74/2.91  fof(c_0_27, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 2.74/2.91  fof(c_0_28, plain, ![X57, X58]:k1_setfam_1(k2_tarski(X57,X58))=k3_xboole_0(X57,X58), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 2.74/2.91  fof(c_0_29, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 2.74/2.91  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.74/2.91  cnf(c_0_31, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.74/2.91  cnf(c_0_32, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.74/2.91  cnf(c_0_33, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 2.74/2.91  fof(c_0_34, plain, ![X37, X38]:m1_subset_1(k6_subset_1(X37,X38),k1_zfmisc_1(X37)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 2.74/2.91  fof(c_0_35, plain, ![X49, X50]:k6_subset_1(X49,X50)=k4_xboole_0(X49,X50), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 2.74/2.91  fof(c_0_36, plain, ![X22]:k4_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t3_boole])).
% 2.74/2.91  fof(c_0_37, plain, ![X51, X52, X53]:(~m1_subset_1(X52,k1_zfmisc_1(X51))|k7_subset_1(X51,X52,X53)=k4_xboole_0(X52,X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 2.74/2.91  cnf(c_0_38, plain, (X3!=k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 2.74/2.91  fof(c_0_39, plain, ![X29, X30]:k2_tarski(X29,X30)=k2_tarski(X30,X29), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 2.74/2.91  fof(c_0_40, plain, ![X26]:k4_xboole_0(k1_xboole_0,X26)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 2.74/2.91  fof(c_0_41, plain, ![X18, X19]:r1_tarski(k3_xboole_0(X18,X19),X18), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 2.74/2.91  fof(c_0_42, plain, ![X59, X60]:((~m1_subset_1(X59,k1_zfmisc_1(X60))|r1_tarski(X59,X60))&(~r1_tarski(X59,X60)|m1_subset_1(X59,k1_zfmisc_1(X60)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 2.74/2.91  fof(c_0_43, plain, ![X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(X35))|m1_subset_1(k3_subset_1(X35,X36),k1_zfmisc_1(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 2.74/2.91  cnf(c_0_44, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.74/2.91  cnf(c_0_45, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.74/2.91  cnf(c_0_46, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.74/2.91  cnf(c_0_47, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.74/2.91  fof(c_0_48, plain, ![X61, X62]:(~l1_pre_topc(X61)|~m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))|m1_subset_1(k2_pre_topc(X61,X62),k1_zfmisc_1(u1_struct_0(X61)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 2.74/2.91  fof(c_0_49, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 2.74/2.91  fof(c_0_50, plain, ![X44, X45, X46]:(~m1_subset_1(X45,k1_zfmisc_1(X44))|(~r2_hidden(X46,X45)|r2_hidden(X46,X44))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 2.74/2.91  cnf(c_0_51, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_38])).
% 2.74/2.91  cnf(c_0_52, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 2.74/2.91  cnf(c_0_53, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.74/2.91  cnf(c_0_54, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.74/2.91  fof(c_0_55, plain, ![X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(X33))|k3_subset_1(X33,X34)=k4_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 2.74/2.91  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.74/2.91  cnf(c_0_57, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.74/2.91  cnf(c_0_58, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_33])).
% 2.74/2.91  cnf(c_0_59, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_46, c_0_33])).
% 2.74/2.91  cnf(c_0_60, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_47, c_0_33])).
% 2.74/2.91  cnf(c_0_61, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.74/2.91  cnf(c_0_62, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 2.74/2.91  fof(c_0_63, negated_conjecture, ((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))&(v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_49])])])).
% 2.74/2.91  cnf(c_0_64, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 2.74/2.91  cnf(c_0_65, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2))))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 2.74/2.91  cnf(c_0_66, plain, (k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_53, c_0_33])).
% 2.74/2.91  cnf(c_0_67, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.74/2.91  cnf(c_0_68, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_54, c_0_31])).
% 2.74/2.91  fof(c_0_69, plain, ![X24, X25]:k4_xboole_0(X24,k3_xboole_0(X24,X25))=k4_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 2.74/2.91  cnf(c_0_70, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 2.74/2.91  cnf(c_0_71, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 2.74/2.91  cnf(c_0_72, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 2.74/2.91  fof(c_0_73, plain, ![X20, X21]:k2_xboole_0(X20,k3_xboole_0(X20,X21))=X20, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 2.74/2.91  fof(c_0_74, plain, ![X31, X32]:k3_tarski(k2_tarski(X31,X32))=k2_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 2.74/2.91  fof(c_0_75, plain, ![X23]:(~r1_tarski(X23,k1_xboole_0)|X23=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 2.74/2.91  fof(c_0_76, plain, ![X27, X28]:k2_xboole_0(X27,X28)=k5_xboole_0(X27,k4_xboole_0(X28,X27)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 2.74/2.91  fof(c_0_77, plain, ![X74, X75]:(~l1_pre_topc(X74)|(~m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(X74)))|k1_tops_1(X74,X75)=k7_subset_1(u1_struct_0(X74),X75,k2_tops_1(X74,X75)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 2.74/2.91  cnf(c_0_78, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 2.74/2.91  cnf(c_0_79, plain, (r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_56, c_0_62])).
% 2.74/2.91  cnf(c_0_80, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 2.74/2.91  cnf(c_0_81, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 2.74/2.91  cnf(c_0_82, plain, (r2_hidden(X1,X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_64, c_0_61])).
% 2.74/2.91  cnf(c_0_83, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 2.74/2.91  cnf(c_0_84, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_67, c_0_33])).
% 2.74/2.91  cnf(c_0_85, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_68, c_0_52])).
% 2.74/2.91  cnf(c_0_86, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 2.74/2.91  cnf(c_0_87, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_70, c_0_33])).
% 2.74/2.91  cnf(c_0_88, plain, (r1_tarski(k3_subset_1(X1,X1),X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 2.74/2.91  cnf(c_0_89, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_73])).
% 2.74/2.91  cnf(c_0_90, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 2.74/2.91  cnf(c_0_91, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 2.74/2.91  fof(c_0_92, plain, ![X63, X64]:(~l1_pre_topc(X63)|(~m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))|r1_tarski(X64,k2_pre_topc(X63,X64)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 2.74/2.91  cnf(c_0_93, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 2.74/2.91  cnf(c_0_94, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 2.74/2.91  cnf(c_0_95, plain, (~r1_tarski(X1,X2)|~r2_hidden(X3,k7_subset_1(X2,X1,X4))|~r2_hidden(X3,X4)), inference(spm,[status(thm)],[c_0_51, c_0_78])).
% 2.74/2.91  cnf(c_0_96, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 2.74/2.91  cnf(c_0_97, negated_conjecture, (r1_tarski(k2_pre_topc(esk3_0,esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])])).
% 2.74/2.91  cnf(c_0_98, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))), inference(spm,[status(thm)],[c_0_82, c_0_68])).
% 2.74/2.91  cnf(c_0_99, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_66])).
% 2.74/2.91  cnf(c_0_100, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2)))), inference(spm,[status(thm)],[c_0_82, c_0_85])).
% 2.74/2.91  cnf(c_0_101, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2)))))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_31]), c_0_33]), c_0_33])).
% 2.74/2.91  cnf(c_0_102, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_87, c_0_61])).
% 2.74/2.91  cnf(c_0_103, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1)))=k3_subset_1(X1,X1)), inference(spm,[status(thm)],[c_0_87, c_0_72])).
% 2.74/2.91  cnf(c_0_104, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_subset_1(X2,X2))), inference(spm,[status(thm)],[c_0_82, c_0_88])).
% 2.74/2.91  cnf(c_0_105, plain, (k3_tarski(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90]), c_0_31])).
% 2.74/2.91  cnf(c_0_106, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_91, c_0_85])).
% 2.74/2.91  cnf(c_0_107, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_92])).
% 2.74/2.91  fof(c_0_108, plain, ![X69, X70, X71]:(~l1_pre_topc(X69)|(~m1_subset_1(X70,k1_zfmisc_1(u1_struct_0(X69)))|(~m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X69)))|(~v3_pre_topc(X70,X69)|~r1_tarski(X70,X71)|r1_tarski(X70,k1_tops_1(X69,X71)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 2.74/2.91  cnf(c_0_109, plain, (k3_tarski(k2_tarski(X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_90]), c_0_33])).
% 2.74/2.91  cnf(c_0_110, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0))=k1_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_80]), c_0_81])])).
% 2.74/2.91  cnf(c_0_111, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)=k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_60, c_0_80])).
% 2.74/2.91  cnf(c_0_112, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,k2_tops_1(esk3_0,esk4_0))|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97])])).
% 2.74/2.91  cnf(c_0_113, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X3,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 2.74/2.91  cnf(c_0_114, plain, (k1_setfam_1(k2_tarski(X1,X2))=k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4)))|r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_tarski(X1,X2))),X3)|r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_tarski(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_100, c_0_84])).
% 2.74/2.91  cnf(c_0_115, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_68])])).
% 2.74/2.91  cnf(c_0_116, plain, (~r2_hidden(X1,k3_subset_1(X2,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_103]), c_0_104])).
% 2.74/2.91  cnf(c_0_117, plain, (k3_tarski(k2_tarski(X1,k1_xboole_0))=X1), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 2.74/2.91  cnf(c_0_118, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.74/2.91  cnf(c_0_119, negated_conjecture, (r1_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_80]), c_0_81])])).
% 2.74/2.91  cnf(c_0_120, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_108])).
% 2.74/2.91  cnf(c_0_121, plain, (k5_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_101]), c_0_52]), c_0_105])).
% 2.74/2.91  cnf(c_0_122, negated_conjecture, (k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0))))=k1_tops_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_110, c_0_111])).
% 2.74/2.91  cnf(c_0_123, negated_conjecture, (k1_setfam_1(k2_tarski(k2_tops_1(esk3_0,esk4_0),X1))=k1_xboole_0|v3_pre_topc(esk4_0,esk3_0)|~r2_hidden(esk1_3(k1_xboole_0,X2,k1_setfam_1(k2_tarski(k2_tops_1(esk3_0,esk4_0),X1))),esk4_0)), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 2.74/2.91  cnf(c_0_124, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_subset_1(X3,k1_setfam_1(k2_tarski(X3,X4)))|r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_tarski(X1,X2))),X2)|r2_hidden(esk1_3(X3,X4,k1_setfam_1(k2_tarski(X1,X2))),X3)), inference(rw,[status(thm)],[c_0_114, c_0_115])).
% 2.74/2.91  cnf(c_0_125, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_91, c_0_68])).
% 2.74/2.91  cnf(c_0_126, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_116, c_0_99])).
% 2.74/2.91  cnf(c_0_127, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2))))=k3_tarski(k2_tarski(X1,X2))), inference(spm,[status(thm)],[c_0_109, c_0_52])).
% 2.74/2.91  cnf(c_0_128, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_59, c_0_106])).
% 2.74/2.91  cnf(c_0_129, plain, (k3_tarski(k2_tarski(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_117, c_0_52])).
% 2.74/2.91  fof(c_0_130, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.74/2.91  cnf(c_0_131, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_56, c_0_58])).
% 2.74/2.91  cnf(c_0_132, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_118, c_0_33])).
% 2.74/2.91  cnf(c_0_133, negated_conjecture, (r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_82, c_0_119])).
% 2.74/2.91  cnf(c_0_134, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))|~v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_80]), c_0_81])])).
% 2.74/2.91  cnf(c_0_135, negated_conjecture, (k5_xboole_0(k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0))),k1_tops_1(esk3_0,esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 2.74/2.91  cnf(c_0_136, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0)))=k1_xboole_0|v3_pre_topc(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_52]), c_0_52]), c_0_125]), c_0_126]), c_0_52])]), c_0_83])).
% 2.74/2.91  cnf(c_0_137, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_125]), c_0_128]), c_0_129])).
% 2.74/2.91  cnf(c_0_138, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_130])).
% 2.74/2.91  cnf(c_0_139, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_130])).
% 2.74/2.91  cnf(c_0_140, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_131, c_0_122])).
% 2.74/2.91  cnf(c_0_141, negated_conjecture, (X1=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k2_pre_topc(esk3_0,esk4_0))))|r2_hidden(esk1_3(X2,k2_pre_topc(esk3_0,esk4_0),X1),X1)|~r2_hidden(esk1_3(X2,k2_pre_topc(esk3_0,esk4_0),X1),esk4_0)), inference(spm,[status(thm)],[c_0_132, c_0_133])).
% 2.74/2.91  cnf(c_0_142, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 2.74/2.91  fof(c_0_143, plain, ![X65, X66]:(~v2_pre_topc(X65)|~l1_pre_topc(X65)|~m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))|v3_pre_topc(k1_tops_1(X65,X66),X65)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 2.74/2.91  fof(c_0_144, plain, ![X67, X68]:(~l1_pre_topc(X67)|(~m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))|k2_tops_1(X67,X68)=k7_subset_1(u1_struct_0(X67),k2_pre_topc(X67,X68),k1_tops_1(X67,X68)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 2.74/2.91  cnf(c_0_145, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))|~v3_pre_topc(X1,esk3_0)|~r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_134, c_0_61])).
% 2.74/2.91  cnf(c_0_146, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0|v3_pre_topc(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_136]), c_0_137])).
% 2.74/2.91  cnf(c_0_147, negated_conjecture, (r1_tarski(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_56, c_0_80])).
% 2.74/2.91  cnf(c_0_148, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_138])).
% 2.74/2.91  cnf(c_0_149, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0|~r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_139, c_0_140])).
% 2.74/2.91  cnf(c_0_150, negated_conjecture, (k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0))))=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_142]), c_0_83])).
% 2.74/2.91  cnf(c_0_151, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_143])).
% 2.74/2.91  cnf(c_0_152, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 2.74/2.91  cnf(c_0_153, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_144])).
% 2.74/2.91  cnf(c_0_154, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_146]), c_0_147]), c_0_148])]), c_0_149])).
% 2.74/2.91  cnf(c_0_155, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 2.74/2.91  cnf(c_0_156, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[c_0_78, c_0_115])).
% 2.74/2.91  cnf(c_0_157, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0)))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_150]), c_0_128])).
% 2.74/2.91  cnf(c_0_158, negated_conjecture, (v3_pre_topc(k1_tops_1(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_80]), c_0_152]), c_0_81])])).
% 2.74/2.91  cnf(c_0_159, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)=k2_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_154]), c_0_81]), c_0_80])])).
% 2.74/2.91  cnf(c_0_160, negated_conjecture, (k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0)!=k2_tops_1(esk3_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_156]), c_0_52]), c_0_157]), c_0_97])])).
% 2.74/2.91  cnf(c_0_161, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)), inference(rw,[status(thm)],[c_0_158, c_0_154])).
% 2.74/2.91  cnf(c_0_162, negated_conjecture, (k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0)=k2_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_159]), c_0_52]), c_0_157]), c_0_97])])).
% 2.74/2.91  cnf(c_0_163, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_160, c_0_161])]), c_0_162])]), ['proof']).
% 2.74/2.91  # SZS output end CNFRefutation
% 2.74/2.91  # Proof object total steps             : 164
% 2.74/2.91  # Proof object clause steps            : 109
% 2.74/2.91  # Proof object formula steps           : 55
% 2.74/2.91  # Proof object conjectures             : 34
% 2.74/2.91  # Proof object clause conjectures      : 31
% 2.74/2.91  # Proof object formula conjectures     : 3
% 2.74/2.91  # Proof object initial clauses used    : 35
% 2.74/2.91  # Proof object initial formulas used   : 27
% 2.74/2.91  # Proof object generating inferences   : 54
% 2.74/2.91  # Proof object simplifying inferences  : 74
% 2.74/2.91  # Training examples: 0 positive, 0 negative
% 2.74/2.91  # Parsed axioms                        : 32
% 2.74/2.91  # Removed by relevancy pruning/SinE    : 0
% 2.74/2.91  # Initial clauses                      : 45
% 2.74/2.91  # Removed in clause preprocessing      : 4
% 2.74/2.91  # Initial clauses in saturation        : 41
% 2.74/2.91  # Processed clauses                    : 23647
% 2.74/2.91  # ...of these trivial                  : 1271
% 2.74/2.91  # ...subsumed                          : 18972
% 2.74/2.91  # ...remaining for further processing  : 3403
% 2.74/2.91  # Other redundant clauses eliminated   : 494
% 2.74/2.91  # Clauses deleted for lack of memory   : 0
% 2.74/2.91  # Backward-subsumed                    : 228
% 2.74/2.91  # Backward-rewritten                   : 664
% 2.74/2.91  # Generated clauses                    : 239488
% 2.74/2.91  # ...of the previous two non-trivial   : 206101
% 2.74/2.91  # Contextual simplify-reflections      : 121
% 2.74/2.91  # Paramodulations                      : 238771
% 2.74/2.91  # Factorizations                       : 124
% 2.74/2.91  # Equation resolutions                 : 590
% 2.74/2.91  # Propositional unsat checks           : 0
% 2.74/2.91  #    Propositional check models        : 0
% 2.74/2.91  #    Propositional check unsatisfiable : 0
% 2.74/2.91  #    Propositional clauses             : 0
% 2.74/2.91  #    Propositional clauses after purity: 0
% 2.74/2.91  #    Propositional unsat core size     : 0
% 2.74/2.91  #    Propositional preprocessing time  : 0.000
% 2.74/2.91  #    Propositional encoding time       : 0.000
% 2.74/2.91  #    Propositional solver time         : 0.000
% 2.74/2.91  #    Success case prop preproc time    : 0.000
% 2.74/2.91  #    Success case prop encoding time   : 0.000
% 2.74/2.91  #    Success case prop solver time     : 0.000
% 2.74/2.91  # Current number of processed clauses  : 2466
% 2.74/2.91  #    Positive orientable unit clauses  : 249
% 2.74/2.91  #    Positive unorientable unit clauses: 4
% 2.74/2.91  #    Negative unit clauses             : 35
% 2.74/2.91  #    Non-unit-clauses                  : 2178
% 2.74/2.91  # Current number of unprocessed clauses: 178517
% 2.74/2.91  # ...number of literals in the above   : 701253
% 2.74/2.91  # Current number of archived formulas  : 0
% 2.74/2.91  # Current number of archived clauses   : 939
% 2.74/2.91  # Clause-clause subsumption calls (NU) : 935003
% 2.74/2.91  # Rec. Clause-clause subsumption calls : 545153
% 2.74/2.91  # Non-unit clause-clause subsumptions  : 9692
% 2.74/2.91  # Unit Clause-clause subsumption calls : 9687
% 2.74/2.91  # Rewrite failures with RHS unbound    : 0
% 2.74/2.91  # BW rewrite match attempts            : 1501
% 2.74/2.91  # BW rewrite match successes           : 150
% 2.74/2.91  # Condensation attempts                : 0
% 2.74/2.91  # Condensation successes               : 0
% 2.74/2.91  # Termbank termtop insertions          : 4979623
% 2.74/2.92  
% 2.74/2.92  # -------------------------------------------------
% 2.74/2.92  # User time                : 2.504 s
% 2.74/2.92  # System time              : 0.075 s
% 2.74/2.92  # Total time               : 2.578 s
% 2.74/2.92  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
