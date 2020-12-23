%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:22 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 314 expanded)
%              Number of clauses        :   43 ( 132 expanded)
%              Number of leaves         :    9 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  209 (1100 expanded)
%              Number of equality atoms :   55 ( 340 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(t55_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( v3_pre_topc(X4,X2)
                     => k1_tops_1(X2,X4) = X4 )
                    & ( k1_tops_1(X1,X3) = X3
                     => v3_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(c_0_9,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_10,plain,(
    ! [X28,X29] : k1_setfam_1(k2_tarski(X28,X29)) = k3_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_11,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | k7_subset_1(X25,X26,X27) = k4_xboole_0(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

cnf(c_0_19,plain,
    ( X3 != k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_16])).

fof(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ v3_pre_topc(esk3_0,esk2_0)
      | k2_tops_1(esk2_0,esk3_0) != k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) )
    & ( v3_pre_topc(esk3_0,esk2_0)
      | k2_tops_1(esk2_0,esk3_0) = k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_22,plain,(
    ! [X38,X39] :
      ( ~ l1_pre_topc(X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
      | k1_tops_1(X38,X39) = k7_subset_1(u1_struct_0(X38),X39,k2_tops_1(X38,X39)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( X1 != k7_subset_1(X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X5,X1)
    | ~ r2_hidden(X5,X4) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( X1 != k7_subset_1(u1_struct_0(esk2_0),esk3_0,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_30,plain,(
    ! [X34,X35,X36,X37] :
      ( ( ~ v3_pre_topc(X37,X35)
        | k1_tops_1(X35,X37) = X37
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X35)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( k1_tops_1(X34,X36) != X36
        | v3_pre_topc(X36,X34)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X35)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

cnf(c_0_31,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,k7_subset_1(X2,X1,X4))
    | ~ r2_hidden(X3,X4) ),
    inference(spm,[status(thm)],[c_0_26,c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | k2_tops_1(esk2_0,esk3_0) = k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_33,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | m1_subset_1(k2_pre_topc(X30,X31),k1_zfmisc_1(u1_struct_0(X30))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_tops_1(X2,X1)))) = k1_tops_1(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_27])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(X1,k7_subset_1(u1_struct_0(esk2_0),esk3_0,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,plain,
    ( k1_tops_1(X2,X1) = X1
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(k2_pre_topc(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(X1,k2_tops_1(esk2_0,esk3_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_34,c_0_16])).

cnf(c_0_44,plain,
    ( k1_tops_1(X1,X2) = X2
    | r2_hidden(esk1_3(X2,k2_tops_1(X1,X2),X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_45,plain,(
    ! [X32,X33] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | k2_tops_1(X32,X33) = k7_subset_1(u1_struct_0(X32),k2_pre_topc(X32,X33),k1_tops_1(X32,X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_46,plain,
    ( v3_pre_topc(X2,X1)
    | k1_tops_1(X1,X2) != X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(X1,k1_tops_1(esk2_0,esk3_0))
    | ~ r2_hidden(X1,k2_tops_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_27]),c_0_38]),c_0_25])])).

cnf(c_0_48,negated_conjecture,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_25]),c_0_40]),c_0_38])])).

cnf(c_0_49,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | ~ r2_hidden(X1,k2_tops_1(esk2_0,esk3_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_38]),c_0_25])])).

cnf(c_0_50,plain,
    ( X1 = k1_tops_1(X2,X3)
    | r2_hidden(esk1_3(X3,k2_tops_1(X2,X3),X1),k2_tops_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(esk1_3(X3,k2_tops_1(X2,X3),X1),X1)
    | ~ r2_hidden(esk1_3(X3,k2_tops_1(X2,X3),X1),X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_35])).

cnf(c_0_51,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = esk3_0
    | r2_hidden(esk1_3(esk3_0,k2_tops_1(esk2_0,esk3_0),esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_25]),c_0_38])])).

cnf(c_0_52,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( v3_pre_topc(X1,X2)
    | k1_tops_1(X2,X1) != X1
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_25]),c_0_38])])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(X1,k2_tops_1(esk2_0,esk3_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_38]),c_0_25])]),c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = esk3_0
    | r2_hidden(esk1_3(esk3_0,k2_tops_1(esk2_0,esk3_0),esk3_0),k2_tops_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_38]),c_0_25])]),c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | k2_tops_1(esk2_0,esk3_0) != k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) = k2_tops_1(X1,X2)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | k1_tops_1(esk2_0,esk3_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_25]),c_0_40]),c_0_38])])).

cnf(c_0_59,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_38]),c_0_25])])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:22:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 2.68/2.89  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 2.68/2.89  # and selection function PSelectComplexExceptUniqMaxHorn.
% 2.68/2.89  #
% 2.68/2.89  # Preprocessing time       : 0.028 s
% 2.68/2.89  
% 2.68/2.89  # Proof found!
% 2.68/2.89  # SZS status Theorem
% 2.68/2.89  # SZS output start CNFRefutation
% 2.68/2.89  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.68/2.89  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.68/2.89  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.68/2.89  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.68/2.89  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 2.68/2.89  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 2.68/2.89  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 2.68/2.89  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.68/2.89  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 2.68/2.89  fof(c_0_9, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 2.68/2.89  fof(c_0_10, plain, ![X28, X29]:k1_setfam_1(k2_tarski(X28,X29))=k3_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 2.68/2.89  fof(c_0_11, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 2.68/2.89  cnf(c_0_12, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.68/2.89  cnf(c_0_13, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.68/2.89  fof(c_0_14, plain, ![X25, X26, X27]:(~m1_subset_1(X26,k1_zfmisc_1(X25))|k7_subset_1(X25,X26,X27)=k4_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 2.68/2.89  cnf(c_0_15, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.68/2.89  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 2.68/2.89  cnf(c_0_17, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.68/2.89  fof(c_0_18, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 2.68/2.89  cnf(c_0_19, plain, (X3!=k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 2.68/2.89  cnf(c_0_20, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_17, c_0_16])).
% 2.68/2.89  fof(c_0_21, negated_conjecture, ((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)!=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0))&(v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 2.68/2.89  fof(c_0_22, plain, ![X38, X39]:(~l1_pre_topc(X38)|(~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|k1_tops_1(X38,X39)=k7_subset_1(u1_struct_0(X38),X39,k2_tops_1(X38,X39)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 2.68/2.89  cnf(c_0_23, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.68/2.89  cnf(c_0_24, plain, (X1!=k7_subset_1(X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X5,X1)|~r2_hidden(X5,X4)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 2.68/2.89  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.68/2.89  cnf(c_0_26, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_19])).
% 2.68/2.89  cnf(c_0_27, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.68/2.89  cnf(c_0_28, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_23, c_0_16])).
% 2.68/2.89  cnf(c_0_29, negated_conjecture, (X1!=k7_subset_1(u1_struct_0(esk2_0),esk3_0,X2)|~r2_hidden(X3,X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 2.68/2.89  fof(c_0_30, plain, ![X34, X35, X36, X37]:((~v3_pre_topc(X37,X35)|k1_tops_1(X35,X37)=X37|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|~l1_pre_topc(X35)|(~v2_pre_topc(X34)|~l1_pre_topc(X34)))&(k1_tops_1(X34,X36)!=X36|v3_pre_topc(X36,X34)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|~l1_pre_topc(X35)|(~v2_pre_topc(X34)|~l1_pre_topc(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 2.68/2.89  cnf(c_0_31, plain, (~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,k7_subset_1(X2,X1,X4))|~r2_hidden(X3,X4)), inference(spm,[status(thm)],[c_0_26, c_0_20])).
% 2.68/2.89  cnf(c_0_32, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.68/2.89  fof(c_0_33, plain, ![X30, X31]:(~l1_pre_topc(X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|m1_subset_1(k2_pre_topc(X30,X31),k1_zfmisc_1(u1_struct_0(X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 2.68/2.89  cnf(c_0_34, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.68/2.89  cnf(c_0_35, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_tops_1(X2,X1))))=k1_tops_1(X2,X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_20, c_0_27])).
% 2.68/2.89  cnf(c_0_36, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_28])).
% 2.68/2.89  cnf(c_0_37, negated_conjecture, (~r2_hidden(X1,k7_subset_1(u1_struct_0(esk2_0),esk3_0,X2))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_29])).
% 2.68/2.89  cnf(c_0_38, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.68/2.89  cnf(c_0_39, plain, (k1_tops_1(X2,X1)=X1|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X2)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.68/2.89  cnf(c_0_40, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.68/2.89  cnf(c_0_41, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(k2_pre_topc(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(X1,k2_tops_1(esk2_0,esk3_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 2.68/2.89  cnf(c_0_42, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.68/2.89  cnf(c_0_43, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_34, c_0_16])).
% 2.68/2.89  cnf(c_0_44, plain, (k1_tops_1(X1,X2)=X2|r2_hidden(esk1_3(X2,k2_tops_1(X1,X2),X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 2.68/2.89  fof(c_0_45, plain, ![X32, X33]:(~l1_pre_topc(X32)|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|k2_tops_1(X32,X33)=k7_subset_1(u1_struct_0(X32),k2_pre_topc(X32,X33),k1_tops_1(X32,X33)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 2.68/2.89  cnf(c_0_46, plain, (v3_pre_topc(X2,X1)|k1_tops_1(X1,X2)!=X2|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.68/2.89  cnf(c_0_47, negated_conjecture, (~r2_hidden(X1,k1_tops_1(esk2_0,esk3_0))|~r2_hidden(X1,k2_tops_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_27]), c_0_38]), c_0_25])])).
% 2.68/2.89  cnf(c_0_48, negated_conjecture, (k1_tops_1(X1,X2)=X2|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_25]), c_0_40]), c_0_38])])).
% 2.68/2.89  cnf(c_0_49, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|~r2_hidden(X1,k2_tops_1(esk2_0,esk3_0))|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_38]), c_0_25])])).
% 2.68/2.89  cnf(c_0_50, plain, (X1=k1_tops_1(X2,X3)|r2_hidden(esk1_3(X3,k2_tops_1(X2,X3),X1),k2_tops_1(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(esk1_3(X3,k2_tops_1(X2,X3),X1),X1)|~r2_hidden(esk1_3(X3,k2_tops_1(X2,X3),X1),X3)), inference(spm,[status(thm)],[c_0_43, c_0_35])).
% 2.68/2.89  cnf(c_0_51, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=esk3_0|r2_hidden(esk1_3(esk3_0,k2_tops_1(esk2_0,esk3_0),esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_25]), c_0_38])])).
% 2.68/2.89  cnf(c_0_52, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 2.68/2.89  cnf(c_0_53, negated_conjecture, (v3_pre_topc(X1,X2)|k1_tops_1(X2,X1)!=X1|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_25]), c_0_38])])).
% 2.68/2.89  cnf(c_0_54, negated_conjecture, (~r2_hidden(X1,k2_tops_1(esk2_0,esk3_0))|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_38]), c_0_25])]), c_0_49])).
% 2.68/2.89  cnf(c_0_55, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=esk3_0|r2_hidden(esk1_3(esk3_0,k2_tops_1(esk2_0,esk3_0),esk3_0),k2_tops_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_38]), c_0_25])]), c_0_51])).
% 2.68/2.89  cnf(c_0_56, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)!=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.68/2.89  cnf(c_0_57, negated_conjecture, (k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)=k2_tops_1(X1,X2)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_52, c_0_48])).
% 2.68/2.89  cnf(c_0_58, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|k1_tops_1(esk2_0,esk3_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_25]), c_0_40]), c_0_38])])).
% 2.68/2.89  cnf(c_0_59, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_51])).
% 2.68/2.89  cnf(c_0_60, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_38]), c_0_25])])).
% 2.68/2.89  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])]), c_0_60]), ['proof']).
% 2.68/2.89  # SZS output end CNFRefutation
% 2.68/2.89  # Proof object total steps             : 62
% 2.68/2.89  # Proof object clause steps            : 43
% 2.68/2.89  # Proof object formula steps           : 19
% 2.68/2.89  # Proof object conjectures             : 23
% 2.68/2.89  # Proof object clause conjectures      : 20
% 2.68/2.89  # Proof object formula conjectures     : 3
% 2.68/2.89  # Proof object initial clauses used    : 16
% 2.68/2.89  # Proof object initial formulas used   : 9
% 2.68/2.89  # Proof object generating inferences   : 21
% 2.68/2.89  # Proof object simplifying inferences  : 36
% 2.68/2.89  # Training examples: 0 positive, 0 negative
% 2.68/2.89  # Parsed axioms                        : 14
% 2.68/2.89  # Removed by relevancy pruning/SinE    : 0
% 2.68/2.89  # Initial clauses                      : 26
% 2.68/2.89  # Removed in clause preprocessing      : 2
% 2.68/2.89  # Initial clauses in saturation        : 24
% 2.68/2.89  # Processed clauses                    : 2143
% 2.68/2.89  # ...of these trivial                  : 40
% 2.68/2.89  # ...subsumed                          : 1373
% 2.68/2.89  # ...remaining for further processing  : 730
% 2.68/2.89  # Other redundant clauses eliminated   : 2127
% 2.68/2.89  # Clauses deleted for lack of memory   : 0
% 2.68/2.89  # Backward-subsumed                    : 79
% 2.68/2.89  # Backward-rewritten                   : 62
% 2.68/2.89  # Generated clauses                    : 112761
% 2.68/2.89  # ...of the previous two non-trivial   : 108264
% 2.68/2.89  # Contextual simplify-reflections      : 24
% 2.68/2.89  # Paramodulations                      : 109252
% 2.68/2.89  # Factorizations                       : 1294
% 2.68/2.89  # Equation resolutions                 : 2211
% 2.68/2.89  # Propositional unsat checks           : 0
% 2.68/2.89  #    Propositional check models        : 0
% 2.68/2.89  #    Propositional check unsatisfiable : 0
% 2.68/2.89  #    Propositional clauses             : 0
% 2.68/2.89  #    Propositional clauses after purity: 0
% 2.68/2.89  #    Propositional unsat core size     : 0
% 2.68/2.89  #    Propositional preprocessing time  : 0.000
% 2.68/2.89  #    Propositional encoding time       : 0.000
% 2.68/2.89  #    Propositional solver time         : 0.000
% 2.68/2.89  #    Success case prop preproc time    : 0.000
% 2.68/2.89  #    Success case prop encoding time   : 0.000
% 2.68/2.89  #    Success case prop solver time     : 0.000
% 2.68/2.89  # Current number of processed clauses  : 583
% 2.68/2.89  #    Positive orientable unit clauses  : 21
% 2.68/2.89  #    Positive unorientable unit clauses: 4
% 2.68/2.89  #    Negative unit clauses             : 12
% 2.68/2.89  #    Non-unit-clauses                  : 546
% 2.68/2.89  # Current number of unprocessed clauses: 105903
% 2.68/2.89  # ...number of literals in the above   : 766048
% 2.68/2.89  # Current number of archived formulas  : 0
% 2.68/2.89  # Current number of archived clauses   : 147
% 2.68/2.89  # Clause-clause subsumption calls (NU) : 108336
% 2.68/2.89  # Rec. Clause-clause subsumption calls : 25946
% 2.68/2.89  # Non-unit clause-clause subsumptions  : 1079
% 2.68/2.89  # Unit Clause-clause subsumption calls : 2229
% 2.68/2.89  # Rewrite failures with RHS unbound    : 17
% 2.68/2.89  # BW rewrite match attempts            : 298
% 2.68/2.89  # BW rewrite match successes           : 44
% 2.68/2.89  # Condensation attempts                : 0
% 2.68/2.89  # Condensation successes               : 0
% 2.68/2.89  # Termbank termtop insertions          : 3246565
% 2.68/2.90  
% 2.68/2.90  # -------------------------------------------------
% 2.68/2.90  # User time                : 2.442 s
% 2.68/2.90  # System time              : 0.067 s
% 2.68/2.90  # Total time               : 2.509 s
% 2.68/2.90  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
