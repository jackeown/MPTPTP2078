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
% DateTime   : Thu Dec  3 11:11:22 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 313 expanded)
%              Number of clauses        :   41 ( 132 expanded)
%              Number of leaves         :    9 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  210 (1101 expanded)
%              Number of equality atoms :   59 ( 342 expanded)
%              Maximal formula depth    :   16 (   5 average)
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

fof(c_0_9,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_10,plain,(
    ! [X29,X30] : k1_setfam_1(k2_tarski(X29,X30)) = k3_xboole_0(X29,X30) ),
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
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | k7_subset_1(X26,X27,X28) = k4_xboole_0(X27,X28) ) ),
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

cnf(c_0_18,plain,
    ( X3 != k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_16])).

fof(c_0_20,plain,(
    ! [X31,X32] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | m1_subset_1(k2_pre_topc(X31,X32),k1_zfmisc_1(u1_struct_0(X31))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_21,plain,
    ( X1 != k7_subset_1(X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X5,X1)
    | ~ r2_hidden(X5,X4) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X33,X34] :
      ( ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | k2_tops_1(X33,X34) = k7_subset_1(u1_struct_0(X33),k2_pre_topc(X33,X34),k1_tops_1(X33,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

fof(c_0_25,plain,(
    ! [X39,X40] :
      ( ~ l1_pre_topc(X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
      | k1_tops_1(X39,X40) = k7_subset_1(u1_struct_0(X39),X40,k2_tops_1(X39,X40)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,plain,
    ( X1 != k7_subset_1(u1_struct_0(X2),k2_pre_topc(X2,X3),X4)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X5,X1)
    | ~ r2_hidden(X5,X4) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ v3_pre_topc(esk3_0,esk2_0)
      | k2_tops_1(esk2_0,esk3_0) != k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) )
    & ( v3_pre_topc(esk3_0,esk2_0)
      | k2_tops_1(esk2_0,esk3_0) = k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_30,plain,(
    ! [X35,X36,X37,X38] :
      ( ( ~ v3_pre_topc(X38,X36)
        | k1_tops_1(X36,X38) = X38
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_pre_topc(X36)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( k1_tops_1(X35,X37) != X37
        | v3_pre_topc(X37,X35)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_pre_topc(X36)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

cnf(c_0_31,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_33,plain,
    ( X1 != k2_tops_1(X2,X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X4,k1_tops_1(X2,X3))
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k1_tops_1(X2,X1) = X1
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | k2_tops_1(esk2_0,esk3_0) = k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_tops_1(X2,X1)))) = k1_tops_1(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_31])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( X1 != k2_tops_1(esk2_0,esk3_0)
    | ~ r2_hidden(X2,k1_tops_1(esk2_0,esk3_0))
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_43,negated_conjecture,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_34]),c_0_37]),c_0_35])])).

cnf(c_0_44,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | X1 != k2_tops_1(esk2_0,esk3_0)
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_38]),c_0_35]),c_0_34])])).

cnf(c_0_45,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_39,c_0_16])).

cnf(c_0_46,plain,
    ( k1_tops_1(X1,X2) = X2
    | r2_hidden(esk1_3(X2,k2_tops_1(X1,X2),X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( v3_pre_topc(X2,X1)
    | k1_tops_1(X1,X2) != X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_48,negated_conjecture,
    ( X1 != k2_tops_1(esk2_0,esk3_0)
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X2,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_35]),c_0_34])]),c_0_44])).

cnf(c_0_49,plain,
    ( X1 = k1_tops_1(X2,X3)
    | r2_hidden(esk1_3(X3,k2_tops_1(X2,X3),X1),k2_tops_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(esk1_3(X3,k2_tops_1(X2,X3),X1),X1)
    | ~ r2_hidden(esk1_3(X3,k2_tops_1(X2,X3),X1),X3) ),
    inference(spm,[status(thm)],[c_0_45,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = esk3_0
    | r2_hidden(esk1_3(esk3_0,k2_tops_1(esk2_0,esk3_0),esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_34]),c_0_35])])).

cnf(c_0_51,negated_conjecture,
    ( v3_pre_topc(X1,X2)
    | k1_tops_1(X2,X1) != X1
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_34]),c_0_35])])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(X1,k2_tops_1(esk2_0,esk3_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = esk3_0
    | r2_hidden(esk1_3(esk3_0,k2_tops_1(esk2_0,esk3_0),esk3_0),k2_tops_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_35]),c_0_34])]),c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | k2_tops_1(esk2_0,esk3_0) != k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_55,negated_conjecture,
    ( k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) = k2_tops_1(X1,X2)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | k1_tops_1(esk2_0,esk3_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_34]),c_0_37]),c_0_35])])).

cnf(c_0_57,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_35]),c_0_34])])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 3.15/3.39  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 3.15/3.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 3.15/3.39  #
% 3.15/3.39  # Preprocessing time       : 0.028 s
% 3.15/3.39  
% 3.15/3.39  # Proof found!
% 3.15/3.39  # SZS status Theorem
% 3.15/3.39  # SZS output start CNFRefutation
% 3.15/3.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.15/3.39  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.15/3.39  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.15/3.39  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.15/3.39  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.15/3.39  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 3.15/3.39  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 3.15/3.39  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 3.15/3.39  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 3.15/3.39  fof(c_0_9, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 3.15/3.39  fof(c_0_10, plain, ![X29, X30]:k1_setfam_1(k2_tarski(X29,X30))=k3_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 3.15/3.39  fof(c_0_11, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 3.15/3.39  cnf(c_0_12, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.15/3.39  cnf(c_0_13, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 3.15/3.39  fof(c_0_14, plain, ![X26, X27, X28]:(~m1_subset_1(X27,k1_zfmisc_1(X26))|k7_subset_1(X26,X27,X28)=k4_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 3.15/3.39  cnf(c_0_15, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 3.15/3.39  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 3.15/3.39  cnf(c_0_17, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.15/3.39  cnf(c_0_18, plain, (X3!=k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 3.15/3.39  cnf(c_0_19, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_17, c_0_16])).
% 3.15/3.39  fof(c_0_20, plain, ![X31, X32]:(~l1_pre_topc(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|m1_subset_1(k2_pre_topc(X31,X32),k1_zfmisc_1(u1_struct_0(X31)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 3.15/3.39  cnf(c_0_21, plain, (X1!=k7_subset_1(X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X5,X1)|~r2_hidden(X5,X4)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 3.15/3.39  cnf(c_0_22, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.15/3.39  fof(c_0_23, plain, ![X33, X34]:(~l1_pre_topc(X33)|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|k2_tops_1(X33,X34)=k7_subset_1(u1_struct_0(X33),k2_pre_topc(X33,X34),k1_tops_1(X33,X34)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 3.15/3.39  fof(c_0_24, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 3.15/3.39  fof(c_0_25, plain, ![X39, X40]:(~l1_pre_topc(X39)|(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|k1_tops_1(X39,X40)=k7_subset_1(u1_struct_0(X39),X40,k2_tops_1(X39,X40)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 3.15/3.39  cnf(c_0_26, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 3.15/3.39  cnf(c_0_27, plain, (X1!=k7_subset_1(u1_struct_0(X2),k2_pre_topc(X2,X3),X4)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X5,X1)|~r2_hidden(X5,X4)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 3.15/3.39  cnf(c_0_28, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.15/3.39  fof(c_0_29, negated_conjecture, ((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)!=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0))&(v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 3.15/3.39  fof(c_0_30, plain, ![X35, X36, X37, X38]:((~v3_pre_topc(X38,X36)|k1_tops_1(X36,X38)=X38|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|~l1_pre_topc(X36)|(~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(k1_tops_1(X35,X37)!=X37|v3_pre_topc(X37,X35)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|~l1_pre_topc(X36)|(~v2_pre_topc(X35)|~l1_pre_topc(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 3.15/3.39  cnf(c_0_31, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.15/3.39  cnf(c_0_32, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_26, c_0_16])).
% 3.15/3.39  cnf(c_0_33, plain, (X1!=k2_tops_1(X2,X3)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X4,k1_tops_1(X2,X3))|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 3.15/3.39  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.15/3.39  cnf(c_0_35, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.15/3.39  cnf(c_0_36, plain, (k1_tops_1(X2,X1)=X1|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X2)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.15/3.39  cnf(c_0_37, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.15/3.39  cnf(c_0_38, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.15/3.39  cnf(c_0_39, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 3.15/3.39  cnf(c_0_40, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_tops_1(X2,X1))))=k1_tops_1(X2,X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_19, c_0_31])).
% 3.15/3.39  cnf(c_0_41, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_32])).
% 3.15/3.39  cnf(c_0_42, negated_conjecture, (X1!=k2_tops_1(esk2_0,esk3_0)|~r2_hidden(X2,k1_tops_1(esk2_0,esk3_0))|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 3.15/3.39  cnf(c_0_43, negated_conjecture, (k1_tops_1(X1,X2)=X2|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_34]), c_0_37]), c_0_35])])).
% 3.15/3.39  cnf(c_0_44, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|X1!=k2_tops_1(esk2_0,esk3_0)|~r2_hidden(X2,esk3_0)|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_38]), c_0_35]), c_0_34])])).
% 3.15/3.39  cnf(c_0_45, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_39, c_0_16])).
% 3.15/3.39  cnf(c_0_46, plain, (k1_tops_1(X1,X2)=X2|r2_hidden(esk1_3(X2,k2_tops_1(X1,X2),X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 3.15/3.39  cnf(c_0_47, plain, (v3_pre_topc(X2,X1)|k1_tops_1(X1,X2)!=X2|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.15/3.39  cnf(c_0_48, negated_conjecture, (X1!=k2_tops_1(esk2_0,esk3_0)|~r2_hidden(X2,esk3_0)|~r2_hidden(X2,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_35]), c_0_34])]), c_0_44])).
% 3.15/3.39  cnf(c_0_49, plain, (X1=k1_tops_1(X2,X3)|r2_hidden(esk1_3(X3,k2_tops_1(X2,X3),X1),k2_tops_1(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(esk1_3(X3,k2_tops_1(X2,X3),X1),X1)|~r2_hidden(esk1_3(X3,k2_tops_1(X2,X3),X1),X3)), inference(spm,[status(thm)],[c_0_45, c_0_40])).
% 3.15/3.39  cnf(c_0_50, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=esk3_0|r2_hidden(esk1_3(esk3_0,k2_tops_1(esk2_0,esk3_0),esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_34]), c_0_35])])).
% 3.15/3.39  cnf(c_0_51, negated_conjecture, (v3_pre_topc(X1,X2)|k1_tops_1(X2,X1)!=X1|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_34]), c_0_35])])).
% 3.15/3.39  cnf(c_0_52, negated_conjecture, (~r2_hidden(X1,k2_tops_1(esk2_0,esk3_0))|~r2_hidden(X1,esk3_0)), inference(er,[status(thm)],[c_0_48])).
% 3.15/3.39  cnf(c_0_53, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=esk3_0|r2_hidden(esk1_3(esk3_0,k2_tops_1(esk2_0,esk3_0),esk3_0),k2_tops_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_35]), c_0_34])]), c_0_50])).
% 3.15/3.39  cnf(c_0_54, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)!=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.15/3.39  cnf(c_0_55, negated_conjecture, (k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)=k2_tops_1(X1,X2)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_28, c_0_43])).
% 3.15/3.39  cnf(c_0_56, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|k1_tops_1(esk2_0,esk3_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_34]), c_0_37]), c_0_35])])).
% 3.15/3.39  cnf(c_0_57, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_50])).
% 3.15/3.39  cnf(c_0_58, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_35]), c_0_34])])).
% 3.15/3.39  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])]), c_0_58]), ['proof']).
% 3.15/3.39  # SZS output end CNFRefutation
% 3.15/3.39  # Proof object total steps             : 60
% 3.15/3.39  # Proof object clause steps            : 41
% 3.15/3.39  # Proof object formula steps           : 19
% 3.15/3.39  # Proof object conjectures             : 21
% 3.15/3.39  # Proof object clause conjectures      : 18
% 3.15/3.39  # Proof object formula conjectures     : 3
% 3.15/3.39  # Proof object initial clauses used    : 16
% 3.15/3.39  # Proof object initial formulas used   : 9
% 3.15/3.39  # Proof object generating inferences   : 19
% 3.15/3.39  # Proof object simplifying inferences  : 35
% 3.15/3.39  # Training examples: 0 positive, 0 negative
% 3.15/3.39  # Parsed axioms                        : 14
% 3.15/3.39  # Removed by relevancy pruning/SinE    : 0
% 3.15/3.39  # Initial clauses                      : 26
% 3.15/3.39  # Removed in clause preprocessing      : 2
% 3.15/3.39  # Initial clauses in saturation        : 24
% 3.15/3.39  # Processed clauses                    : 2574
% 3.15/3.39  # ...of these trivial                  : 41
% 3.15/3.39  # ...subsumed                          : 1680
% 3.15/3.39  # ...remaining for further processing  : 853
% 3.15/3.39  # Other redundant clauses eliminated   : 1815
% 3.15/3.39  # Clauses deleted for lack of memory   : 0
% 3.15/3.39  # Backward-subsumed                    : 85
% 3.15/3.39  # Backward-rewritten                   : 99
% 3.15/3.39  # Generated clauses                    : 129651
% 3.15/3.39  # ...of the previous two non-trivial   : 124853
% 3.15/3.39  # Contextual simplify-reflections      : 39
% 3.15/3.39  # Paramodulations                      : 126118
% 3.15/3.39  # Factorizations                       : 1630
% 3.15/3.39  # Equation resolutions                 : 1900
% 3.15/3.39  # Propositional unsat checks           : 0
% 3.15/3.39  #    Propositional check models        : 0
% 3.15/3.39  #    Propositional check unsatisfiable : 0
% 3.15/3.39  #    Propositional clauses             : 0
% 3.15/3.39  #    Propositional clauses after purity: 0
% 3.15/3.39  #    Propositional unsat core size     : 0
% 3.15/3.39  #    Propositional preprocessing time  : 0.000
% 3.15/3.39  #    Propositional encoding time       : 0.000
% 3.15/3.39  #    Propositional solver time         : 0.000
% 3.15/3.39  #    Success case prop preproc time    : 0.000
% 3.15/3.39  #    Success case prop encoding time   : 0.000
% 3.15/3.39  #    Success case prop solver time     : 0.000
% 3.15/3.39  # Current number of processed clauses  : 664
% 3.15/3.39  #    Positive orientable unit clauses  : 31
% 3.15/3.39  #    Positive unorientable unit clauses: 1
% 3.15/3.39  #    Negative unit clauses             : 2
% 3.15/3.39  #    Non-unit-clauses                  : 630
% 3.15/3.39  # Current number of unprocessed clauses: 122051
% 3.15/3.39  # ...number of literals in the above   : 936597
% 3.15/3.39  # Current number of archived formulas  : 0
% 3.15/3.39  # Current number of archived clauses   : 189
% 3.15/3.39  # Clause-clause subsumption calls (NU) : 114018
% 3.15/3.39  # Rec. Clause-clause subsumption calls : 38148
% 3.15/3.39  # Non-unit clause-clause subsumptions  : 1671
% 3.15/3.39  # Unit Clause-clause subsumption calls : 653
% 3.15/3.39  # Rewrite failures with RHS unbound    : 0
% 3.15/3.39  # BW rewrite match attempts            : 174
% 3.15/3.39  # BW rewrite match successes           : 23
% 3.15/3.39  # Condensation attempts                : 0
% 3.15/3.39  # Condensation successes               : 0
% 3.15/3.39  # Termbank termtop insertions          : 4033564
% 3.15/3.40  
% 3.15/3.40  # -------------------------------------------------
% 3.15/3.40  # User time                : 2.984 s
% 3.15/3.40  # System time              : 0.072 s
% 3.15/3.40  # Total time               : 3.056 s
% 3.15/3.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
