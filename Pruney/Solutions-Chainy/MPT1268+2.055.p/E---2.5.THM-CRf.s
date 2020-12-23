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
% DateTime   : Thu Dec  3 11:12:10 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 217 expanded)
%              Number of clauses        :   38 (  82 expanded)
%              Number of leaves         :   11 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  214 (1344 expanded)
%              Number of equality atoms :   24 ( 170 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t86_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X1) )
                 => X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t54_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2,X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,k1_tops_1(X1,X3))
          <=> ? [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                & v3_pre_topc(X4,X1)
                & r1_tarski(X4,X3)
                & r2_hidden(X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(t84_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v2_tops_1(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X1) )
                   => X3 = k1_xboole_0 ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t86_tops_1])).

fof(c_0_12,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(k2_xboole_0(X7,X8),X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_13,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k2_xboole_0(X10,X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_14,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | m1_subset_1(X13,k1_zfmisc_1(X14)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_15,negated_conjecture,(
    ! [X31] :
      ( v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ v2_tops_1(esk4_0,esk3_0) )
      & ( r1_tarski(esk5_0,esk4_0)
        | ~ v2_tops_1(esk4_0,esk3_0) )
      & ( v3_pre_topc(esk5_0,esk3_0)
        | ~ v2_tops_1(esk4_0,esk3_0) )
      & ( esk5_0 != k1_xboole_0
        | ~ v2_tops_1(esk4_0,esk3_0) )
      & ( v2_tops_1(esk4_0,esk3_0)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ r1_tarski(X31,esk4_0)
        | ~ v3_pre_topc(X31,esk3_0)
        | X31 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X21,X22,X23,X25] :
      ( ( m1_subset_1(esk2_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))
        | ~ r2_hidden(X22,k1_tops_1(X21,X23))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( v3_pre_topc(esk2_3(X21,X22,X23),X21)
        | ~ r2_hidden(X22,k1_tops_1(X21,X23))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r1_tarski(esk2_3(X21,X22,X23),X23)
        | ~ r2_hidden(X22,k1_tops_1(X21,X23))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(X22,esk2_3(X21,X22,X23))
        | ~ r2_hidden(X22,k1_tops_1(X21,X23))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v3_pre_topc(X25,X21)
        | ~ r1_tarski(X25,X23)
        | ~ r2_hidden(X22,X25)
        | r2_hidden(X22,k1_tops_1(X21,X23))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_tops_1])])])])])).

cnf(c_0_21,negated_conjecture,
    ( v2_tops_1(esk4_0,esk3_0)
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0)
    | ~ v3_pre_topc(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_25,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | ~ r1_tarski(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_26,plain,
    ( r2_hidden(X4,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v2_tops_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk3_0)
    | ~ v2_tops_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( X1 = k1_xboole_0
    | v2_tops_1(esk4_0,esk3_0)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_33,plain,(
    ! [X17,X18] :
      ( ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | v3_pre_topc(k1_tops_1(X17,X18),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

fof(c_0_34,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | r1_tarski(k1_tops_1(X19,X20),X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_35,plain,(
    ! [X26,X27] :
      ( ( ~ v2_tops_1(X27,X26)
        | k1_tops_1(X26,X27) = k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( k1_tops_1(X26,X27) != k1_xboole_0
        | v2_tops_1(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk3_0,X2))
    | ~ v2_tops_1(esk4_0,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk5_0,X2)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( X1 = k1_xboole_0
    | v2_tops_1(esk4_0,esk3_0)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( k1_tops_1(X2,X1) = k1_xboole_0
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_tops_1(esk4_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk3_0,X1),X2)
    | ~ r1_tarski(esk5_0,X1)
    | ~ r2_hidden(X2,esk5_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | ~ v2_tops_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_44,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_45,plain,
    ( v2_tops_1(X2,X1)
    | k1_tops_1(X1,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( k1_tops_1(esk3_0,X1) = k1_xboole_0
    | v2_tops_1(esk4_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk3_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_28]),c_0_29])])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_19]),c_0_28])])).

cnf(c_0_48,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = k1_xboole_0
    | ~ v2_tops_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_19]),c_0_28])])).

cnf(c_0_49,negated_conjecture,
    ( ~ v2_tops_1(esk4_0,esk3_0)
    | ~ r1_tarski(k1_tops_1(esk3_0,esk4_0),X1)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_19]),c_0_43])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( v2_tops_1(esk4_0,esk3_0)
    | k1_tops_1(esk3_0,esk4_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_19]),c_0_28])])).

cnf(c_0_52,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_19]),c_0_47])]),c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_tops_1(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_48]),c_0_50])])).

cnf(c_0_54,negated_conjecture,
    ( v2_tops_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])])).

fof(c_0_55,plain,(
    ! [X5] :
      ( X5 = k1_xboole_0
      | r2_hidden(esk1_1(X5),X5) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_56,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | ~ v2_tops_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_54])])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:32:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.20/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t86_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v3_pre_topc(X3,X1))=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 0.20/0.39  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.20/0.39  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.39  fof(t54_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k1_tops_1(X1,X3))<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 0.20/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.39  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.20/0.39  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 0.20/0.39  fof(t84_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 0.20/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.39  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.39  fof(c_0_11, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v3_pre_topc(X3,X1))=>X3=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t86_tops_1])).
% 0.20/0.39  fof(c_0_12, plain, ![X7, X8, X9]:(~r1_tarski(k2_xboole_0(X7,X8),X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.20/0.39  fof(c_0_13, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k2_xboole_0(X10,X11)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.39  fof(c_0_14, plain, ![X13, X14]:((~m1_subset_1(X13,k1_zfmisc_1(X14))|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|m1_subset_1(X13,k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.39  fof(c_0_15, negated_conjecture, ![X31]:((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(((m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v2_tops_1(esk4_0,esk3_0))&(((r1_tarski(esk5_0,esk4_0)|~v2_tops_1(esk4_0,esk3_0))&(v3_pre_topc(esk5_0,esk3_0)|~v2_tops_1(esk4_0,esk3_0)))&(esk5_0!=k1_xboole_0|~v2_tops_1(esk4_0,esk3_0))))&(v2_tops_1(esk4_0,esk3_0)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk3_0)))|(~r1_tarski(X31,esk4_0)|~v3_pre_topc(X31,esk3_0)|X31=k1_xboole_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])])).
% 0.20/0.39  cnf(c_0_16, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_18, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  fof(c_0_20, plain, ![X21, X22, X23, X25]:(((((m1_subset_1(esk2_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))|~r2_hidden(X22,k1_tops_1(X21,X23))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(v3_pre_topc(esk2_3(X21,X22,X23),X21)|~r2_hidden(X22,k1_tops_1(X21,X23))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(r1_tarski(esk2_3(X21,X22,X23),X23)|~r2_hidden(X22,k1_tops_1(X21,X23))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(r2_hidden(X22,esk2_3(X21,X22,X23))|~r2_hidden(X22,k1_tops_1(X21,X23))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X21)))|~v3_pre_topc(X25,X21)|~r1_tarski(X25,X23)|~r2_hidden(X22,X25)|r2_hidden(X22,k1_tops_1(X21,X23))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(~v2_pre_topc(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_tops_1])])])])])).
% 0.20/0.39  cnf(c_0_21, negated_conjecture, (v2_tops_1(esk4_0,esk3_0)|X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)|~v3_pre_topc(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_22, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (r1_tarski(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.39  fof(c_0_25, plain, ![X15, X16]:(~r2_hidden(X15,X16)|~r1_tarski(X16,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.39  cnf(c_0_26, plain, (r2_hidden(X4,k1_tops_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|~r1_tarski(X1,X3)|~r2_hidden(X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v2_tops_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (v3_pre_topc(esk5_0,esk3_0)|~v2_tops_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (X1=k1_xboole_0|v2_tops_1(esk4_0,esk3_0)|~v3_pre_topc(X1,esk3_0)|~r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.39  fof(c_0_33, plain, ![X17, X18]:(~v2_pre_topc(X17)|~l1_pre_topc(X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|v3_pre_topc(k1_tops_1(X17,X18),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.20/0.39  fof(c_0_34, plain, ![X19, X20]:(~l1_pre_topc(X19)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|r1_tarski(k1_tops_1(X19,X20),X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.20/0.39  fof(c_0_35, plain, ![X26, X27]:((~v2_tops_1(X27,X26)|k1_tops_1(X26,X27)=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))&(k1_tops_1(X26,X27)!=k1_xboole_0|v2_tops_1(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).
% 0.20/0.39  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk3_0,X2))|~v2_tops_1(esk4_0,esk3_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk5_0,X2)|~r2_hidden(X1,esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (X1=k1_xboole_0|v2_tops_1(esk4_0,esk3_0)|~v3_pre_topc(X1,esk3_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.39  cnf(c_0_39, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.39  cnf(c_0_40, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.39  cnf(c_0_41, plain, (k1_tops_1(X2,X1)=k1_xboole_0|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (~v2_tops_1(esk4_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(k1_tops_1(esk3_0,X1),X2)|~r1_tarski(esk5_0,X1)|~r2_hidden(X2,esk5_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|~v2_tops_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  fof(c_0_44, plain, ![X12]:r1_tarski(k1_xboole_0,X12), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.39  cnf(c_0_45, plain, (v2_tops_1(X2,X1)|k1_tops_1(X1,X2)!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (k1_tops_1(esk3_0,X1)=k1_xboole_0|v2_tops_1(esk4_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(k1_tops_1(esk3_0,X1),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_28]), c_0_29])])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_19]), c_0_28])])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=k1_xboole_0|~v2_tops_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_19]), c_0_28])])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (~v2_tops_1(esk4_0,esk3_0)|~r1_tarski(k1_tops_1(esk3_0,esk4_0),X1)|~r2_hidden(X1,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_19]), c_0_43])).
% 0.20/0.39  cnf(c_0_50, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.39  cnf(c_0_51, negated_conjecture, (v2_tops_1(esk4_0,esk3_0)|k1_tops_1(esk3_0,esk4_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_19]), c_0_28])])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_19]), c_0_47])]), c_0_48])).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (~v2_tops_1(esk4_0,esk3_0)|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_48]), c_0_50])])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (v2_tops_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52])])).
% 0.20/0.39  fof(c_0_55, plain, ![X5]:(X5=k1_xboole_0|r2_hidden(esk1_1(X5),X5)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (esk5_0!=k1_xboole_0|~v2_tops_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_57, negated_conjecture, (~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54])])).
% 0.20/0.39  cnf(c_0_58, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (esk5_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_54])])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 61
% 0.20/0.39  # Proof object clause steps            : 38
% 0.20/0.39  # Proof object formula steps           : 23
% 0.20/0.39  # Proof object conjectures             : 28
% 0.20/0.39  # Proof object clause conjectures      : 25
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 20
% 0.20/0.39  # Proof object initial formulas used   : 11
% 0.20/0.39  # Proof object generating inferences   : 15
% 0.20/0.39  # Proof object simplifying inferences  : 26
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 11
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 24
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 24
% 0.20/0.39  # Processed clauses                    : 218
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 85
% 0.20/0.39  # ...remaining for further processing  : 133
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 26
% 0.20/0.39  # Backward-rewritten                   : 35
% 0.20/0.39  # Generated clauses                    : 357
% 0.20/0.39  # ...of the previous two non-trivial   : 329
% 0.20/0.39  # Contextual simplify-reflections      : 12
% 0.20/0.39  # Paramodulations                      : 357
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 0
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 72
% 0.20/0.39  #    Positive orientable unit clauses  : 10
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 4
% 0.20/0.39  #    Non-unit-clauses                  : 58
% 0.20/0.39  # Current number of unprocessed clauses: 121
% 0.20/0.39  # ...number of literals in the above   : 617
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 61
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 2621
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 859
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 117
% 0.20/0.39  # Unit Clause-clause subsumption calls : 235
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 3
% 0.20/0.39  # BW rewrite match successes           : 3
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 9471
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.043 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.047 s
% 0.20/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
