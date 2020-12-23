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
% DateTime   : Thu Dec  3 11:11:54 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 277 expanded)
%              Number of clauses        :   44 ( 118 expanded)
%              Number of leaves         :   15 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  176 ( 790 expanded)
%              Number of equality atoms :   60 ( 253 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t81_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( v3_pre_topc(X3,X1)
                 => k2_pre_topc(X1,X3) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d3_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = k2_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t41_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
               => k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_15,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X26))
      | k9_subset_1(X26,X27,X28) = k3_xboole_0(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_16,plain,(
    ! [X29,X30] : k1_setfam_1(k2_tarski(X29,X30)) = k3_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v1_tops_1(X2,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( v3_pre_topc(X3,X1)
                   => k2_pre_topc(X1,X3) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X3,X2)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t81_tops_1])).

cnf(c_0_18,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & v1_tops_1(esk3_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & v3_pre_topc(esk4_0,esk2_0)
    & k2_pre_topc(esk2_0,esk4_0) != k2_pre_topc(esk2_0,k9_subset_1(u1_struct_0(esk2_0),esk4_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_21,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_22,plain,(
    ! [X35,X36] :
      ( ( ~ v1_tops_1(X36,X35)
        | k2_pre_topc(X35,X36) = k2_struct_0(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_pre_topc(X35) )
      & ( k2_pre_topc(X35,X36) != k2_struct_0(X35)
        | v1_tops_1(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).

fof(c_0_23,plain,(
    ! [X33] :
      ( ~ l1_struct_0(X33)
      | k2_struct_0(X33) = u1_struct_0(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_24,plain,(
    ! [X34] :
      ( ~ l1_pre_topc(X34)
      | l1_struct_0(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_25,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X20))
      | k9_subset_1(X20,X21,X22) = k9_subset_1(X20,X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_26,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X18,X19] : k2_tarski(X18,X19) = k2_tarski(X19,X18) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | ~ r2_hidden(X25,X24)
      | r2_hidden(X25,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_31,plain,
    ( k2_pre_topc(X2,X1) = k2_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( v1_tops_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,esk4_0)) = k9_subset_1(u1_struct_0(esk2_0),X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_39,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_19])).

cnf(c_0_41,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_42,plain,(
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

fof(c_0_43,plain,(
    ! [X37,X38,X39] :
      ( ~ v2_pre_topc(X37)
      | ~ l1_pre_topc(X37)
      | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
      | ~ v3_pre_topc(X38,X37)
      | k2_pre_topc(X37,k9_subset_1(u1_struct_0(X37),X38,k2_pre_topc(X37,X39))) = k2_pre_topc(X37,k9_subset_1(u1_struct_0(X37),X38,X39)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_tops_1])])])).

cnf(c_0_44,negated_conjecture,
    ( k2_struct_0(esk2_0) = k2_pre_topc(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_45,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,esk3_0)) = k9_subset_1(u1_struct_0(esk2_0),X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),esk4_0,X1) = k9_subset_1(u1_struct_0(esk2_0),X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_27])).

cnf(c_0_48,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),X1,esk4_0) = k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

fof(c_0_49,plain,(
    ! [X31,X32] :
      ( ~ r2_hidden(X31,X32)
      | ~ r1_tarski(X32,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_50,plain,(
    ! [X14] : r1_tarski(k1_xboole_0,X14) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_55,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk3_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_34])])).

cnf(c_0_56,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),X1,esk3_0) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_39]),c_0_40])).

cnf(c_0_57,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),esk4_0,X1) = k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1)) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_61,negated_conjecture,
    ( X1 = k4_xboole_0(esk4_0,X2)
    | r2_hidden(esk1_3(esk4_0,X2,X1),u1_struct_0(esk2_0))
    | r2_hidden(esk1_3(esk4_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk4_0) != k2_pre_topc(esk2_0,k9_subset_1(u1_struct_0(esk2_0),esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_63,negated_conjecture,
    ( k2_pre_topc(esk2_0,k9_subset_1(u1_struct_0(esk2_0),X1,u1_struct_0(esk2_0))) = k2_pre_topc(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_32]),c_0_54]),c_0_34])]),c_0_55]),c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) = k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( X1 = k4_xboole_0(esk4_0,u1_struct_0(esk2_0))
    | r2_hidden(esk1_3(esk4_0,u1_struct_0(esk2_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_68,plain,(
    ! [X15] : k4_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_69,negated_conjecture,
    ( k2_pre_topc(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))) != k2_pre_topc(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_56])).

cnf(c_0_70,negated_conjecture,
    ( k2_pre_topc(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,u1_struct_0(esk2_0)))) = k2_pre_topc(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_57]),c_0_27])]),c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(esk4_0,u1_struct_0(esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( k2_pre_topc(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))) != k2_pre_topc(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:59:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.12/0.39  # and selection function SelectNewComplexAHPNS.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.028 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.12/0.39  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.12/0.39  fof(t81_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X3,X1)=>k2_pre_topc(X1,X3)=k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X3,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tops_1)).
% 0.12/0.39  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.12/0.39  fof(d3_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=k2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 0.12/0.39  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.12/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.12/0.39  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 0.12/0.39  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.12/0.39  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.12/0.39  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.12/0.39  fof(t41_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)=>k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))=k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tops_1)).
% 0.12/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.12/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.39  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.12/0.39  fof(c_0_15, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(X26))|k9_subset_1(X26,X27,X28)=k3_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.12/0.39  fof(c_0_16, plain, ![X29, X30]:k1_setfam_1(k2_tarski(X29,X30))=k3_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.12/0.39  fof(c_0_17, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X3,X1)=>k2_pre_topc(X1,X3)=k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X3,X2)))))))), inference(assume_negation,[status(cth)],[t81_tops_1])).
% 0.12/0.39  cnf(c_0_18, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.39  cnf(c_0_19, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  fof(c_0_20, negated_conjecture, ((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(v1_tops_1(esk3_0,esk2_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(v3_pre_topc(esk4_0,esk2_0)&k2_pre_topc(esk2_0,esk4_0)!=k2_pre_topc(esk2_0,k9_subset_1(u1_struct_0(esk2_0),esk4_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.12/0.39  fof(c_0_21, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.12/0.39  fof(c_0_22, plain, ![X35, X36]:((~v1_tops_1(X36,X35)|k2_pre_topc(X35,X36)=k2_struct_0(X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~l1_pre_topc(X35))&(k2_pre_topc(X35,X36)!=k2_struct_0(X35)|v1_tops_1(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~l1_pre_topc(X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).
% 0.12/0.39  fof(c_0_23, plain, ![X33]:(~l1_struct_0(X33)|k2_struct_0(X33)=u1_struct_0(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.12/0.39  fof(c_0_24, plain, ![X34]:(~l1_pre_topc(X34)|l1_struct_0(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.12/0.39  fof(c_0_25, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(X20))|k9_subset_1(X20,X21,X22)=k9_subset_1(X20,X22,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 0.12/0.39  cnf(c_0_26, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.39  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.39  fof(c_0_28, plain, ![X18, X19]:k2_tarski(X18,X19)=k2_tarski(X19,X18), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.12/0.39  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.39  fof(c_0_30, plain, ![X23, X24, X25]:(~m1_subset_1(X24,k1_zfmisc_1(X23))|(~r2_hidden(X25,X24)|r2_hidden(X25,X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.12/0.39  cnf(c_0_31, plain, (k2_pre_topc(X2,X1)=k2_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.39  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.39  cnf(c_0_33, negated_conjecture, (v1_tops_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.39  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.39  cnf(c_0_35, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.39  cnf(c_0_36, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.39  cnf(c_0_37, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.39  cnf(c_0_38, negated_conjecture, (k1_setfam_1(k2_tarski(X1,esk4_0))=k9_subset_1(u1_struct_0(esk2_0),X1,esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.39  cnf(c_0_39, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.39  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_29, c_0_19])).
% 0.12/0.39  cnf(c_0_41, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.39  fof(c_0_42, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.12/0.39  fof(c_0_43, plain, ![X37, X38, X39]:(~v2_pre_topc(X37)|~l1_pre_topc(X37)|(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|(~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))|(~v3_pre_topc(X38,X37)|k2_pre_topc(X37,k9_subset_1(u1_struct_0(X37),X38,k2_pre_topc(X37,X39)))=k2_pre_topc(X37,k9_subset_1(u1_struct_0(X37),X38,X39)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_tops_1])])])).
% 0.12/0.39  cnf(c_0_44, negated_conjecture, (k2_struct_0(esk2_0)=k2_pre_topc(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])])).
% 0.12/0.39  cnf(c_0_45, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.39  cnf(c_0_46, negated_conjecture, (k1_setfam_1(k2_tarski(X1,esk3_0))=k9_subset_1(u1_struct_0(esk2_0),X1,esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_32])).
% 0.12/0.39  cnf(c_0_47, negated_conjecture, (k9_subset_1(u1_struct_0(esk2_0),esk4_0,X1)=k9_subset_1(u1_struct_0(esk2_0),X1,esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_27])).
% 0.12/0.39  cnf(c_0_48, negated_conjecture, (k9_subset_1(u1_struct_0(esk2_0),X1,esk4_0)=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.12/0.39  fof(c_0_49, plain, ![X31, X32]:(~r2_hidden(X31,X32)|~r1_tarski(X32,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.12/0.39  fof(c_0_50, plain, ![X14]:r1_tarski(k1_xboole_0,X14), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.39  cnf(c_0_51, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_27])).
% 0.12/0.39  cnf(c_0_52, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.12/0.39  cnf(c_0_53, plain, (k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))=k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.12/0.39  cnf(c_0_54, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.39  cnf(c_0_55, negated_conjecture, (k2_pre_topc(esk2_0,esk3_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_34])])).
% 0.12/0.39  cnf(c_0_56, negated_conjecture, (k9_subset_1(u1_struct_0(esk2_0),X1,esk3_0)=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_39]), c_0_40])).
% 0.12/0.39  cnf(c_0_57, negated_conjecture, (k9_subset_1(u1_struct_0(esk2_0),esk4_0,X1)=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.12/0.39  cnf(c_0_58, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.12/0.39  cnf(c_0_59, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.12/0.39  cnf(c_0_60, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.12/0.39  cnf(c_0_61, negated_conjecture, (X1=k4_xboole_0(esk4_0,X2)|r2_hidden(esk1_3(esk4_0,X2,X1),u1_struct_0(esk2_0))|r2_hidden(esk1_3(esk4_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.12/0.39  cnf(c_0_62, negated_conjecture, (k2_pre_topc(esk2_0,esk4_0)!=k2_pre_topc(esk2_0,k9_subset_1(u1_struct_0(esk2_0),esk4_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.39  cnf(c_0_63, negated_conjecture, (k2_pre_topc(esk2_0,k9_subset_1(u1_struct_0(esk2_0),X1,u1_struct_0(esk2_0)))=k2_pre_topc(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)))|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_32]), c_0_54]), c_0_34])]), c_0_55]), c_0_56])).
% 0.12/0.39  cnf(c_0_64, negated_conjecture, (v3_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.39  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.12/0.39  cnf(c_0_66, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.12/0.39  cnf(c_0_67, negated_conjecture, (X1=k4_xboole_0(esk4_0,u1_struct_0(esk2_0))|r2_hidden(esk1_3(esk4_0,u1_struct_0(esk2_0),X1),X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.12/0.39  fof(c_0_68, plain, ![X15]:k4_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.12/0.39  cnf(c_0_69, negated_conjecture, (k2_pre_topc(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))!=k2_pre_topc(esk2_0,esk4_0)), inference(rw,[status(thm)],[c_0_62, c_0_56])).
% 0.12/0.39  cnf(c_0_70, negated_conjecture, (k2_pre_topc(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,u1_struct_0(esk2_0))))=k2_pre_topc(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_57]), c_0_27])]), c_0_65])).
% 0.12/0.39  cnf(c_0_71, negated_conjecture, (k4_xboole_0(esk4_0,u1_struct_0(esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.12/0.39  cnf(c_0_72, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.12/0.39  cnf(c_0_73, negated_conjecture, (k2_pre_topc(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))!=k2_pre_topc(esk2_0,esk4_0)), inference(rw,[status(thm)],[c_0_69, c_0_65])).
% 0.12/0.39  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_73]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 75
% 0.12/0.39  # Proof object clause steps            : 44
% 0.12/0.39  # Proof object formula steps           : 31
% 0.12/0.39  # Proof object conjectures             : 28
% 0.12/0.39  # Proof object clause conjectures      : 25
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 22
% 0.12/0.39  # Proof object initial formulas used   : 15
% 0.12/0.39  # Proof object generating inferences   : 16
% 0.12/0.39  # Proof object simplifying inferences  : 24
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 15
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 27
% 0.12/0.39  # Removed in clause preprocessing      : 1
% 0.12/0.39  # Initial clauses in saturation        : 26
% 0.12/0.39  # Processed clauses                    : 267
% 0.12/0.39  # ...of these trivial                  : 8
% 0.12/0.39  # ...subsumed                          : 121
% 0.12/0.39  # ...remaining for further processing  : 138
% 0.12/0.39  # Other redundant clauses eliminated   : 3
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 5
% 0.12/0.39  # Backward-rewritten                   : 23
% 0.12/0.39  # Generated clauses                    : 823
% 0.12/0.39  # ...of the previous two non-trivial   : 786
% 0.12/0.39  # Contextual simplify-reflections      : 0
% 0.12/0.39  # Paramodulations                      : 808
% 0.12/0.39  # Factorizations                       : 12
% 0.12/0.39  # Equation resolutions                 : 3
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 81
% 0.12/0.39  #    Positive orientable unit clauses  : 20
% 0.12/0.39  #    Positive unorientable unit clauses: 4
% 0.12/0.39  #    Negative unit clauses             : 2
% 0.12/0.39  #    Non-unit-clauses                  : 55
% 0.12/0.39  # Current number of unprocessed clauses: 519
% 0.12/0.39  # ...number of literals in the above   : 1430
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 55
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 927
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 697
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 63
% 0.12/0.39  # Unit Clause-clause subsumption calls : 28
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 107
% 0.12/0.39  # BW rewrite match successes           : 55
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 13692
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.046 s
% 0.12/0.39  # System time              : 0.004 s
% 0.12/0.39  # Total time               : 0.050 s
% 0.12/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
