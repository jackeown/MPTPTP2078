%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:05 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  129 (4602 expanded)
%              Number of clauses        :   82 (2153 expanded)
%              Number of leaves         :   23 (1192 expanded)
%              Depth                    :   19
%              Number of atoms          :  306 (9814 expanded)
%              Number of equality atoms :   69 (3118 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t69_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
           => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t36_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(k3_subset_1(X1,X2),X3)
           => r1_tarski(k3_subset_1(X1,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).

fof(t41_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(t31_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v4_pre_topc(X2,X1)
                  & r1_tarski(X3,X2) )
               => r1_tarski(k2_pre_topc(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

fof(c_0_23,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_24,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_25,plain,(
    ! [X54,X55] :
      ( ( ~ m1_subset_1(X54,k1_zfmisc_1(X55))
        | r1_tarski(X54,X55) )
      & ( ~ r1_tarski(X54,X55)
        | m1_subset_1(X54,k1_zfmisc_1(X55)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_26,plain,(
    ! [X26,X27] : r1_tarski(X26,k2_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_27,plain,(
    ! [X30,X31] : k3_tarski(k2_tarski(X30,X31)) = k2_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_28,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_29,plain,(
    ! [X52,X53] : k1_setfam_1(k2_tarski(X52,X53)) = k3_xboole_0(X52,X53) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t69_tops_1])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X41))
      | ~ m1_subset_1(X43,k1_zfmisc_1(X41))
      | k4_subset_1(X41,X42,X43) = k2_xboole_0(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & v4_pre_topc(esk4_0,esk3_0)
    & ~ r1_tarski(k2_tops_1(esk3_0,esk4_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

cnf(c_0_42,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_43,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | ~ m1_subset_1(X38,k1_zfmisc_1(X36))
      | m1_subset_1(k4_subset_1(X36,X37,X38),k1_zfmisc_1(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X4)
    | X4 != k1_setfam_1(k2_tarski(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_34])).

cnf(c_0_52,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_tarski(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_36])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),u1_struct_0(esk3_0))
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_59,plain,
    ( k4_subset_1(X1,X2,X3) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k4_subset_1(X1,X2,X3)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k4_subset_1(X2,X1,X3)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_55])).

fof(c_0_62,plain,(
    ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(X22,k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r2_hidden(esk1_2(X1,k1_setfam_1(k2_tarski(X2,X3))),X3)
    | ~ r2_hidden(esk1_2(X1,k1_setfam_1(k2_tarski(X2,X3))),X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),X2)
    | r1_tarski(esk4_0,X1)
    | ~ r1_tarski(u1_struct_0(esk3_0),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_58])).

fof(c_0_65,plain,(
    ! [X28,X29] : k2_tarski(X28,X29) = k2_tarski(X29,X28) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_66,plain,
    ( k4_subset_1(X1,X1,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

fof(c_0_67,plain,(
    ! [X39,X40] : m1_subset_1(k6_subset_1(X39,X40),k1_zfmisc_1(X39)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_68,plain,(
    ! [X44,X45] : k6_subset_1(X44,X45) = k4_xboole_0(X44,X45) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_69,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_70,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k4_xboole_0(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ r2_hidden(esk1_2(X1,k1_setfam_1(k2_tarski(X2,X1))),X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_31])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),k3_tarski(k2_tarski(u1_struct_0(esk3_0),X2)))
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_45])).

cnf(c_0_73,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_66]),c_0_61])])).

cnf(c_0_75,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_77,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_69,c_0_39])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_79,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(X32))
      | k3_subset_1(X32,X33) = k4_xboole_0(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k3_tarski(k2_tarski(u1_struct_0(esk3_0),X1))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])).

cnf(c_0_81,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_73])).

cnf(c_0_82,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_83,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_39]),c_0_77]),c_0_77])).

cnf(c_0_84,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)))
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_87,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_84,c_0_77])).

cnf(c_0_88,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,X1)) = esk4_0
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_85]),c_0_86])])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_58]),c_0_73])).

cnf(c_0_90,plain,
    ( k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_87]),c_0_82])])).

cnf(c_0_91,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,esk4_0)) = esk4_0
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_73])).

cnf(c_0_92,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_73])).

cnf(c_0_93,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_89]),c_0_86])])).

cnf(c_0_94,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_73])).

fof(c_0_95,plain,(
    ! [X63,X64] :
      ( ~ l1_pre_topc(X63)
      | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))
      | k2_pre_topc(X63,X64) = k4_subset_1(u1_struct_0(X63),X64,k2_tops_1(X63,X64)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

fof(c_0_96,plain,(
    ! [X61,X62] :
      ( ~ l1_pre_topc(X61)
      | ~ m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))
      | k2_tops_1(X61,X62) = k2_tops_1(X61,k3_subset_1(u1_struct_0(X61),X62)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

fof(c_0_97,plain,(
    ! [X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(X34))
      | m1_subset_1(k3_subset_1(X34,X35),k1_zfmisc_1(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_98,negated_conjecture,
    ( k3_subset_1(X1,k5_xboole_0(X1,esk4_0)) = esk4_0
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_99,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk3_0),esk4_0) = k3_subset_1(u1_struct_0(esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_50])])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(k5_xboole_0(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_93])).

fof(c_0_101,plain,(
    ! [X46,X47,X48] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(X46))
      | ~ m1_subset_1(X48,k1_zfmisc_1(X46))
      | ~ r1_tarski(k3_subset_1(X46,X47),X48)
      | r1_tarski(k3_subset_1(X46,X48),X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_subset_1])])])).

fof(c_0_102,plain,(
    ! [X49,X50,X51] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(X49))
      | ~ m1_subset_1(X51,k1_zfmisc_1(X49))
      | r1_tarski(k3_subset_1(X49,k4_subset_1(X49,X50,X51)),k3_subset_1(X49,X50)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_subset_1])])])).

cnf(c_0_103,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_104,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_105,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_106,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_61])])).

cnf(c_0_107,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_100,c_0_99])).

fof(c_0_109,plain,(
    ! [X56,X57] :
      ( ~ l1_pre_topc(X56)
      | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
      | m1_subset_1(k2_tops_1(X56,X57),k1_zfmisc_1(u1_struct_0(X56))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

fof(c_0_110,plain,(
    ! [X58,X59,X60] :
      ( ~ l1_pre_topc(X58)
      | ~ m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))
      | ~ m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X58)))
      | ~ v4_pre_topc(X59,X58)
      | ~ r1_tarski(X60,X59)
      | r1_tarski(k2_pre_topc(X58,X60),X59) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_1])])])).

cnf(c_0_111,plain,
    ( r1_tarski(k3_subset_1(X2,X3),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(k3_subset_1(X2,X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_112,plain,
    ( r1_tarski(k3_subset_1(X2,k4_subset_1(X2,X1,X3)),k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_113,plain,
    ( k4_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2),k2_tops_1(X1,X2)) = k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_105])).

cnf(c_0_114,negated_conjecture,
    ( k2_tops_1(esk3_0,k3_subset_1(u1_struct_0(esk3_0),esk4_0)) = k2_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_106]),c_0_107]),c_0_108])])).

cnf(c_0_115,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_116,plain,
    ( r1_tarski(k2_pre_topc(X1,X3),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_117,plain,
    ( r1_tarski(k3_subset_1(X1,k3_subset_1(X1,X2)),k4_subset_1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_105]),c_0_52])).

cnf(c_0_118,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0)) = k2_pre_topc(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_106]),c_0_106]),c_0_107]),c_0_108])])).

cnf(c_0_119,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_114]),c_0_107]),c_0_108])])).

cnf(c_0_120,plain,
    ( X1 = k2_pre_topc(X2,X3)
    | ~ v4_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_pre_topc(X2,X3))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_116])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_106]),c_0_119]),c_0_50])])).

cnf(c_0_122,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_123,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_73])).

cnf(c_0_124,negated_conjecture,
    ( k2_pre_topc(esk3_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_122]),c_0_107]),c_0_50]),c_0_55])])).

cnf(c_0_125,plain,
    ( r1_tarski(X1,k4_subset_1(X2,X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_54])).

cnf(c_0_126,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_118,c_0_124])).

cnf(c_0_127,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_128,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_119]),c_0_50])]),c_0_127]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:30:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.45  #
% 0.21/0.45  # Preprocessing time       : 0.028 s
% 0.21/0.45  # Presaturation interreduction done
% 0.21/0.45  
% 0.21/0.45  # Proof found!
% 0.21/0.45  # SZS status Theorem
% 0.21/0.45  # SZS output start CNFRefutation
% 0.21/0.45  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.45  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.45  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.21/0.45  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.21/0.45  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.21/0.45  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.21/0.45  fof(t69_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 0.21/0.45  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.21/0.45  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 0.21/0.45  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.45  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.21/0.45  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 0.21/0.45  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.21/0.45  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.45  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.21/0.45  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 0.21/0.45  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 0.21/0.45  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.21/0.45  fof(t36_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X3)=>r1_tarski(k3_subset_1(X1,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_subset_1)).
% 0.21/0.45  fof(t41_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 0.21/0.45  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 0.21/0.45  fof(t31_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)&r1_tarski(X3,X2))=>r1_tarski(k2_pre_topc(X1,X3),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_1)).
% 0.21/0.45  fof(c_0_23, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.45  fof(c_0_24, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.45  fof(c_0_25, plain, ![X54, X55]:((~m1_subset_1(X54,k1_zfmisc_1(X55))|r1_tarski(X54,X55))&(~r1_tarski(X54,X55)|m1_subset_1(X54,k1_zfmisc_1(X55)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.45  fof(c_0_26, plain, ![X26, X27]:r1_tarski(X26,k2_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.21/0.45  fof(c_0_27, plain, ![X30, X31]:k3_tarski(k2_tarski(X30,X31))=k2_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.21/0.45  fof(c_0_28, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.21/0.45  fof(c_0_29, plain, ![X52, X53]:k1_setfam_1(k2_tarski(X52,X53))=k3_xboole_0(X52,X53), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.21/0.45  cnf(c_0_30, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.45  cnf(c_0_31, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.45  fof(c_0_32, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t69_tops_1])).
% 0.21/0.45  cnf(c_0_33, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.45  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.45  cnf(c_0_35, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.45  cnf(c_0_36, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.45  fof(c_0_37, plain, ![X41, X42, X43]:(~m1_subset_1(X42,k1_zfmisc_1(X41))|~m1_subset_1(X43,k1_zfmisc_1(X41))|k4_subset_1(X41,X42,X43)=k2_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.21/0.45  cnf(c_0_38, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.45  cnf(c_0_39, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.45  cnf(c_0_40, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.45  fof(c_0_41, negated_conjecture, (l1_pre_topc(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(v4_pre_topc(esk4_0,esk3_0)&~r1_tarski(k2_tops_1(esk3_0,esk4_0),esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 0.21/0.45  cnf(c_0_42, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.45  fof(c_0_43, plain, ![X36, X37, X38]:(~m1_subset_1(X37,k1_zfmisc_1(X36))|~m1_subset_1(X38,k1_zfmisc_1(X36))|m1_subset_1(k4_subset_1(X36,X37,X38),k1_zfmisc_1(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 0.21/0.45  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.45  cnf(c_0_45, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.45  cnf(c_0_46, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.45  cnf(c_0_47, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.45  cnf(c_0_48, plain, (r2_hidden(X1,X4)|X4!=k1_setfam_1(k2_tarski(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.45  cnf(c_0_49, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_40, c_0_34])).
% 0.21/0.45  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.45  cnf(c_0_51, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_42, c_0_34])).
% 0.21/0.45  cnf(c_0_52, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.45  cnf(c_0_53, plain, (m1_subset_1(X1,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2))))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.45  cnf(c_0_54, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_tarski(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_46, c_0_36])).
% 0.21/0.45  cnf(c_0_55, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_47])).
% 0.21/0.45  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.45  cnf(c_0_57, plain, (r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_48])).
% 0.21/0.45  cnf(c_0_58, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),u1_struct_0(esk3_0))|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.45  cnf(c_0_59, plain, (k4_subset_1(X1,X2,X3)=X1|~m1_subset_1(X1,k1_zfmisc_1(k4_subset_1(X1,X2,X3)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.45  cnf(c_0_60, plain, (m1_subset_1(X1,k1_zfmisc_1(k4_subset_1(X2,X1,X3)))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.45  cnf(c_0_61, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_55])).
% 0.21/0.45  fof(c_0_62, plain, ![X22, X23]:k4_xboole_0(X22,X23)=k5_xboole_0(X22,k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.45  cnf(c_0_63, plain, (r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))|~r2_hidden(esk1_2(X1,k1_setfam_1(k2_tarski(X2,X3))),X3)|~r2_hidden(esk1_2(X1,k1_setfam_1(k2_tarski(X2,X3))),X2)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.45  cnf(c_0_64, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),X2)|r1_tarski(esk4_0,X1)|~r1_tarski(u1_struct_0(esk3_0),X2)), inference(spm,[status(thm)],[c_0_30, c_0_58])).
% 0.21/0.45  fof(c_0_65, plain, ![X28, X29]:k2_tarski(X28,X29)=k2_tarski(X29,X28), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.21/0.45  cnf(c_0_66, plain, (k4_subset_1(X1,X1,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])])).
% 0.21/0.45  fof(c_0_67, plain, ![X39, X40]:m1_subset_1(k6_subset_1(X39,X40),k1_zfmisc_1(X39)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 0.21/0.45  fof(c_0_68, plain, ![X44, X45]:k6_subset_1(X44,X45)=k4_xboole_0(X44,X45), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.21/0.45  cnf(c_0_69, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.21/0.45  fof(c_0_70, plain, ![X24, X25]:k4_xboole_0(X24,k4_xboole_0(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.45  cnf(c_0_71, plain, (r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X1)))|~r2_hidden(esk1_2(X1,k1_setfam_1(k2_tarski(X2,X1))),X2)), inference(spm,[status(thm)],[c_0_63, c_0_31])).
% 0.21/0.45  cnf(c_0_72, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),k3_tarski(k2_tarski(u1_struct_0(esk3_0),X2)))|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_64, c_0_45])).
% 0.21/0.45  cnf(c_0_73, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.21/0.45  cnf(c_0_74, plain, (k3_tarski(k2_tarski(X1,X2))=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_66]), c_0_61])])).
% 0.21/0.45  cnf(c_0_75, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.21/0.45  cnf(c_0_76, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.21/0.45  cnf(c_0_77, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_69, c_0_39])).
% 0.21/0.45  cnf(c_0_78, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.21/0.45  fof(c_0_79, plain, ![X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(X32))|k3_subset_1(X32,X33)=k4_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.21/0.45  cnf(c_0_80, negated_conjecture, (r1_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k3_tarski(k2_tarski(u1_struct_0(esk3_0),X1)))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])).
% 0.21/0.45  cnf(c_0_81, plain, (k3_tarski(k2_tarski(X1,X2))=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_74, c_0_73])).
% 0.21/0.45  cnf(c_0_82, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76]), c_0_77])).
% 0.21/0.45  cnf(c_0_83, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_39]), c_0_77]), c_0_77])).
% 0.21/0.45  cnf(c_0_84, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.21/0.45  cnf(c_0_85, negated_conjecture, (r1_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)))|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.21/0.45  cnf(c_0_86, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.21/0.45  cnf(c_0_87, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_84, c_0_77])).
% 0.21/0.45  cnf(c_0_88, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,X1))=esk4_0|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_85]), c_0_86])])).
% 0.21/0.45  cnf(c_0_89, negated_conjecture, (r1_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_58]), c_0_73])).
% 0.21/0.45  cnf(c_0_90, plain, (k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_87]), c_0_82])])).
% 0.21/0.45  cnf(c_0_91, negated_conjecture, (k1_setfam_1(k2_tarski(X1,esk4_0))=esk4_0|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_88, c_0_73])).
% 0.21/0.45  cnf(c_0_92, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_87, c_0_73])).
% 0.21/0.45  cnf(c_0_93, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_89]), c_0_86])])).
% 0.21/0.45  cnf(c_0_94, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_82, c_0_73])).
% 0.21/0.45  fof(c_0_95, plain, ![X63, X64]:(~l1_pre_topc(X63)|(~m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))|k2_pre_topc(X63,X64)=k4_subset_1(u1_struct_0(X63),X64,k2_tops_1(X63,X64)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 0.21/0.45  fof(c_0_96, plain, ![X61, X62]:(~l1_pre_topc(X61)|(~m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))|k2_tops_1(X61,X62)=k2_tops_1(X61,k3_subset_1(u1_struct_0(X61),X62)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 0.21/0.45  fof(c_0_97, plain, ![X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(X34))|m1_subset_1(k3_subset_1(X34,X35),k1_zfmisc_1(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.21/0.45  cnf(c_0_98, negated_conjecture, (k3_subset_1(X1,k5_xboole_0(X1,esk4_0))=esk4_0|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.21/0.45  cnf(c_0_99, negated_conjecture, (k5_xboole_0(u1_struct_0(esk3_0),esk4_0)=k3_subset_1(u1_struct_0(esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_50])])).
% 0.21/0.45  cnf(c_0_100, negated_conjecture, (m1_subset_1(k5_xboole_0(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_94, c_0_93])).
% 0.21/0.45  fof(c_0_101, plain, ![X46, X47, X48]:(~m1_subset_1(X47,k1_zfmisc_1(X46))|(~m1_subset_1(X48,k1_zfmisc_1(X46))|(~r1_tarski(k3_subset_1(X46,X47),X48)|r1_tarski(k3_subset_1(X46,X48),X47)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_subset_1])])])).
% 0.21/0.45  fof(c_0_102, plain, ![X49, X50, X51]:(~m1_subset_1(X50,k1_zfmisc_1(X49))|(~m1_subset_1(X51,k1_zfmisc_1(X49))|r1_tarski(k3_subset_1(X49,k4_subset_1(X49,X50,X51)),k3_subset_1(X49,X50)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_subset_1])])])).
% 0.21/0.45  cnf(c_0_103, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.21/0.45  cnf(c_0_104, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.21/0.45  cnf(c_0_105, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.21/0.45  cnf(c_0_106, negated_conjecture, (k3_subset_1(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_61])])).
% 0.21/0.45  cnf(c_0_107, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.45  cnf(c_0_108, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[c_0_100, c_0_99])).
% 0.21/0.45  fof(c_0_109, plain, ![X56, X57]:(~l1_pre_topc(X56)|~m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))|m1_subset_1(k2_tops_1(X56,X57),k1_zfmisc_1(u1_struct_0(X56)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 0.21/0.45  fof(c_0_110, plain, ![X58, X59, X60]:(~l1_pre_topc(X58)|(~m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))|(~m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X58)))|(~v4_pre_topc(X59,X58)|~r1_tarski(X60,X59)|r1_tarski(k2_pre_topc(X58,X60),X59))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_1])])])).
% 0.21/0.45  cnf(c_0_111, plain, (r1_tarski(k3_subset_1(X2,X3),X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(k3_subset_1(X2,X1),X3)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.21/0.45  cnf(c_0_112, plain, (r1_tarski(k3_subset_1(X2,k4_subset_1(X2,X1,X3)),k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.21/0.45  cnf(c_0_113, plain, (k4_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2),k2_tops_1(X1,X2))=k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_105])).
% 0.21/0.45  cnf(c_0_114, negated_conjecture, (k2_tops_1(esk3_0,k3_subset_1(u1_struct_0(esk3_0),esk4_0))=k2_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_106]), c_0_107]), c_0_108])])).
% 0.21/0.45  cnf(c_0_115, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.21/0.45  cnf(c_0_116, plain, (r1_tarski(k2_pre_topc(X1,X3),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_110])).
% 0.21/0.45  cnf(c_0_117, plain, (r1_tarski(k3_subset_1(X1,k3_subset_1(X1,X2)),k4_subset_1(X1,X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_105]), c_0_52])).
% 0.21/0.45  cnf(c_0_118, negated_conjecture, (k4_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0))=k2_pre_topc(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_106]), c_0_106]), c_0_107]), c_0_108])])).
% 0.21/0.45  cnf(c_0_119, negated_conjecture, (m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_114]), c_0_107]), c_0_108])])).
% 0.21/0.45  cnf(c_0_120, plain, (X1=k2_pre_topc(X2,X3)|~v4_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_pre_topc(X2,X3))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_33, c_0_116])).
% 0.21/0.45  cnf(c_0_121, negated_conjecture, (r1_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_106]), c_0_119]), c_0_50])])).
% 0.21/0.45  cnf(c_0_122, negated_conjecture, (v4_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.45  cnf(c_0_123, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_45, c_0_73])).
% 0.21/0.45  cnf(c_0_124, negated_conjecture, (k2_pre_topc(esk3_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_122]), c_0_107]), c_0_50]), c_0_55])])).
% 0.21/0.45  cnf(c_0_125, plain, (r1_tarski(X1,k4_subset_1(X2,X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_123, c_0_54])).
% 0.21/0.45  cnf(c_0_126, negated_conjecture, (k4_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[c_0_118, c_0_124])).
% 0.21/0.45  cnf(c_0_127, negated_conjecture, (~r1_tarski(k2_tops_1(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.45  cnf(c_0_128, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_119]), c_0_50])]), c_0_127]), ['proof']).
% 0.21/0.45  # SZS output end CNFRefutation
% 0.21/0.45  # Proof object total steps             : 129
% 0.21/0.45  # Proof object clause steps            : 82
% 0.21/0.45  # Proof object formula steps           : 47
% 0.21/0.45  # Proof object conjectures             : 28
% 0.21/0.45  # Proof object clause conjectures      : 25
% 0.21/0.45  # Proof object formula conjectures     : 3
% 0.21/0.45  # Proof object initial clauses used    : 30
% 0.21/0.45  # Proof object initial formulas used   : 23
% 0.21/0.45  # Proof object generating inferences   : 41
% 0.21/0.45  # Proof object simplifying inferences  : 57
% 0.21/0.45  # Training examples: 0 positive, 0 negative
% 0.21/0.45  # Parsed axioms                        : 23
% 0.21/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.45  # Initial clauses                      : 36
% 0.21/0.45  # Removed in clause preprocessing      : 4
% 0.21/0.45  # Initial clauses in saturation        : 32
% 0.21/0.45  # Processed clauses                    : 705
% 0.21/0.45  # ...of these trivial                  : 25
% 0.21/0.45  # ...subsumed                          : 368
% 0.21/0.45  # ...remaining for further processing  : 312
% 0.21/0.45  # Other redundant clauses eliminated   : 5
% 0.21/0.45  # Clauses deleted for lack of memory   : 0
% 0.21/0.45  # Backward-subsumed                    : 6
% 0.21/0.45  # Backward-rewritten                   : 12
% 0.21/0.45  # Generated clauses                    : 3016
% 0.21/0.45  # ...of the previous two non-trivial   : 2664
% 0.21/0.45  # Contextual simplify-reflections      : 15
% 0.21/0.45  # Paramodulations                      : 2997
% 0.21/0.45  # Factorizations                       : 14
% 0.21/0.45  # Equation resolutions                 : 5
% 0.21/0.45  # Propositional unsat checks           : 0
% 0.21/0.45  #    Propositional check models        : 0
% 0.21/0.45  #    Propositional check unsatisfiable : 0
% 0.21/0.45  #    Propositional clauses             : 0
% 0.21/0.45  #    Propositional clauses after purity: 0
% 0.21/0.45  #    Propositional unsat core size     : 0
% 0.21/0.45  #    Propositional preprocessing time  : 0.000
% 0.21/0.45  #    Propositional encoding time       : 0.000
% 0.21/0.45  #    Propositional solver time         : 0.000
% 0.21/0.45  #    Success case prop preproc time    : 0.000
% 0.21/0.45  #    Success case prop encoding time   : 0.000
% 0.21/0.45  #    Success case prop solver time     : 0.000
% 0.21/0.45  # Current number of processed clauses  : 258
% 0.21/0.45  #    Positive orientable unit clauses  : 52
% 0.21/0.45  #    Positive unorientable unit clauses: 1
% 0.21/0.45  #    Negative unit clauses             : 4
% 0.21/0.45  #    Non-unit-clauses                  : 201
% 0.21/0.45  # Current number of unprocessed clauses: 1998
% 0.21/0.45  # ...number of literals in the above   : 7337
% 0.21/0.45  # Current number of archived formulas  : 0
% 0.21/0.45  # Current number of archived clauses   : 53
% 0.21/0.45  # Clause-clause subsumption calls (NU) : 7231
% 0.21/0.45  # Rec. Clause-clause subsumption calls : 4971
% 0.21/0.45  # Non-unit clause-clause subsumptions  : 368
% 0.21/0.45  # Unit Clause-clause subsumption calls : 221
% 0.21/0.45  # Rewrite failures with RHS unbound    : 0
% 0.21/0.45  # BW rewrite match attempts            : 70
% 0.21/0.45  # BW rewrite match successes           : 20
% 0.21/0.45  # Condensation attempts                : 0
% 0.21/0.45  # Condensation successes               : 0
% 0.21/0.45  # Termbank termtop insertions          : 51926
% 0.21/0.45  
% 0.21/0.45  # -------------------------------------------------
% 0.21/0.45  # User time                : 0.104 s
% 0.21/0.45  # System time              : 0.005 s
% 0.21/0.45  # Total time               : 0.108 s
% 0.21/0.45  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
