%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:59 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 159 expanded)
%              Number of clauses        :   51 (  72 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :   20
%              Number of atoms          :  277 ( 585 expanded)
%              Number of equality atoms :   19 (  50 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(t24_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(t56_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(k3_tarski(X1),X2)
        & r2_hidden(X3,X1) )
     => r1_tarski(X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(t100_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(c_0_15,plain,(
    ! [X26,X27,X28] :
      ( ~ r2_hidden(X26,X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X28))
      | ~ v1_xboole_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_16,plain,(
    ! [X38] :
      ( ~ l1_pre_topc(X38)
      | m1_subset_1(u1_pre_topc(X38),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X38)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_17,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X18,X19)
      | v1_xboole_0(X19)
      | r2_hidden(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_18,plain,(
    ! [X17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X17)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_24,plain,(
    ! [X11,X12] :
      ( ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(k3_tarski(X11),X12) )
      & ( ~ r1_tarski(esk2_2(X11,X12),X12)
        | r1_tarski(k3_tarski(X11),X12) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

cnf(c_0_25,plain,
    ( ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

fof(c_0_28,plain,(
    ! [X29,X30] :
      ( ~ r2_hidden(X29,X30)
      | ~ r1_tarski(X30,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X31,X32,X33,X34] :
      ( ( r2_hidden(u1_struct_0(X31),u1_pre_topc(X31))
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( ~ m1_subset_1(X32,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X31))))
        | ~ r1_tarski(X32,u1_pre_topc(X31))
        | r2_hidden(k5_setfam_1(u1_struct_0(X31),X32),u1_pre_topc(X31))
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ r2_hidden(X33,u1_pre_topc(X31))
        | ~ r2_hidden(X34,u1_pre_topc(X31))
        | r2_hidden(k9_subset_1(u1_struct_0(X31),X33,X34),u1_pre_topc(X31))
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( m1_subset_1(esk4_1(X31),k1_zfmisc_1(u1_struct_0(X31)))
        | m1_subset_1(esk3_1(X31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X31))))
        | ~ r2_hidden(u1_struct_0(X31),u1_pre_topc(X31))
        | v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( m1_subset_1(esk5_1(X31),k1_zfmisc_1(u1_struct_0(X31)))
        | m1_subset_1(esk3_1(X31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X31))))
        | ~ r2_hidden(u1_struct_0(X31),u1_pre_topc(X31))
        | v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( r2_hidden(esk4_1(X31),u1_pre_topc(X31))
        | m1_subset_1(esk3_1(X31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X31))))
        | ~ r2_hidden(u1_struct_0(X31),u1_pre_topc(X31))
        | v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( r2_hidden(esk5_1(X31),u1_pre_topc(X31))
        | m1_subset_1(esk3_1(X31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X31))))
        | ~ r2_hidden(u1_struct_0(X31),u1_pre_topc(X31))
        | v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X31),esk4_1(X31),esk5_1(X31)),u1_pre_topc(X31))
        | m1_subset_1(esk3_1(X31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X31))))
        | ~ r2_hidden(u1_struct_0(X31),u1_pre_topc(X31))
        | v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( m1_subset_1(esk4_1(X31),k1_zfmisc_1(u1_struct_0(X31)))
        | r1_tarski(esk3_1(X31),u1_pre_topc(X31))
        | ~ r2_hidden(u1_struct_0(X31),u1_pre_topc(X31))
        | v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( m1_subset_1(esk5_1(X31),k1_zfmisc_1(u1_struct_0(X31)))
        | r1_tarski(esk3_1(X31),u1_pre_topc(X31))
        | ~ r2_hidden(u1_struct_0(X31),u1_pre_topc(X31))
        | v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( r2_hidden(esk4_1(X31),u1_pre_topc(X31))
        | r1_tarski(esk3_1(X31),u1_pre_topc(X31))
        | ~ r2_hidden(u1_struct_0(X31),u1_pre_topc(X31))
        | v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( r2_hidden(esk5_1(X31),u1_pre_topc(X31))
        | r1_tarski(esk3_1(X31),u1_pre_topc(X31))
        | ~ r2_hidden(u1_struct_0(X31),u1_pre_topc(X31))
        | v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X31),esk4_1(X31),esk5_1(X31)),u1_pre_topc(X31))
        | r1_tarski(esk3_1(X31),u1_pre_topc(X31))
        | ~ r2_hidden(u1_struct_0(X31),u1_pre_topc(X31))
        | v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( m1_subset_1(esk4_1(X31),k1_zfmisc_1(u1_struct_0(X31)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X31),esk3_1(X31)),u1_pre_topc(X31))
        | ~ r2_hidden(u1_struct_0(X31),u1_pre_topc(X31))
        | v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( m1_subset_1(esk5_1(X31),k1_zfmisc_1(u1_struct_0(X31)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X31),esk3_1(X31)),u1_pre_topc(X31))
        | ~ r2_hidden(u1_struct_0(X31),u1_pre_topc(X31))
        | v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( r2_hidden(esk4_1(X31),u1_pre_topc(X31))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X31),esk3_1(X31)),u1_pre_topc(X31))
        | ~ r2_hidden(u1_struct_0(X31),u1_pre_topc(X31))
        | v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( r2_hidden(esk5_1(X31),u1_pre_topc(X31))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X31),esk3_1(X31)),u1_pre_topc(X31))
        | ~ r2_hidden(u1_struct_0(X31),u1_pre_topc(X31))
        | v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X31),esk4_1(X31),esk5_1(X31)),u1_pre_topc(X31))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X31),esk3_1(X31)),u1_pre_topc(X31))
        | ~ r2_hidden(u1_struct_0(X31),u1_pre_topc(X31))
        | v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_32,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v2_pre_topc(esk6_0)
    & l1_pre_topc(esk6_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk6_0))) != u1_struct_0(esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_27])])])])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k3_tarski(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_41,plain,(
    ! [X16] : k3_tarski(k1_zfmisc_1(X16)) = X16 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_42,plain,
    ( ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | v1_xboole_0(u1_pre_topc(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( v1_xboole_0(k3_tarski(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_33])).

cnf(c_0_46,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_39])])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_47])).

cnf(c_0_50,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_26])).

fof(c_0_51,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(k3_tarski(X23),X24)
      | ~ r2_hidden(X25,X23)
      | r1_tarski(X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_tarski(X1),X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_54,plain,
    ( r2_hidden(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_52])).

fof(c_0_56,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | r1_tarski(k3_tarski(X14),k3_tarski(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_39]),c_0_55])).

fof(c_0_59,plain,(
    ! [X10] : r1_tarski(X10,k1_zfmisc_1(k3_tarski(X10))) ),
    inference(variable_rename,[status(thm)],[t100_zfmisc_1])).

cnf(c_0_60,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk6_0),X1)
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(esk6_0)),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk6_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_46])).

cnf(c_0_65,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_46])).

fof(c_0_67,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k3_tarski(X1),u1_struct_0(esk6_0))
    | ~ r2_hidden(esk2_2(X1,u1_struct_0(esk6_0)),u1_pre_topc(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_70,plain,(
    ! [X39] :
      ( v1_xboole_0(X39)
      | ~ r2_hidden(k3_tarski(X39),X39)
      | k4_yellow_0(k2_yellow_1(X39)) = k3_tarski(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

cnf(c_0_71,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k3_tarski(u1_pre_topc(esk6_0)),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_30])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_74,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk6_0)) = u1_struct_0(esk6_0)
    | ~ r1_tarski(u1_struct_0(esk6_0),k3_tarski(u1_pre_topc(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_73])).

cnf(c_0_77,plain,
    ( k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(csr,[status(thm)],[c_0_74,c_0_29])).

cnf(c_0_78,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk6_0)) = u1_struct_0(esk6_0)
    | ~ r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk6_0))) != u1_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_80,negated_conjecture,
    ( ~ r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_37]),c_0_44]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.029 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.40  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.19/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.40  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.40  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.19/0.40  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_1)).
% 0.19/0.40  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.40  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.19/0.40  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.19/0.40  fof(t56_setfam_1, axiom, ![X1, X2, X3]:((r1_tarski(k3_tarski(X1),X2)&r2_hidden(X3,X1))=>r1_tarski(X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_setfam_1)).
% 0.19/0.40  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.19/0.40  fof(t100_zfmisc_1, axiom, ![X1]:r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 0.19/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.40  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.19/0.40  fof(c_0_15, plain, ![X26, X27, X28]:(~r2_hidden(X26,X27)|~m1_subset_1(X27,k1_zfmisc_1(X28))|~v1_xboole_0(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.40  fof(c_0_16, plain, ![X38]:(~l1_pre_topc(X38)|m1_subset_1(u1_pre_topc(X38),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X38))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.19/0.40  fof(c_0_17, plain, ![X18, X19]:(~m1_subset_1(X18,X19)|(v1_xboole_0(X19)|r2_hidden(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.40  fof(c_0_18, plain, ![X17]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X17)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.40  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_20, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_21, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_22, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  fof(c_0_23, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.40  fof(c_0_24, plain, ![X11, X12]:((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(k3_tarski(X11),X12))&(~r1_tarski(esk2_2(X11,X12),X12)|r1_tarski(k3_tarski(X11),X12))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.19/0.40  cnf(c_0_25, plain, (~l1_pre_topc(X1)|~r2_hidden(X2,u1_pre_topc(X1))|~v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.40  cnf(c_0_26, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))|v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.40  fof(c_0_27, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 0.19/0.40  fof(c_0_28, plain, ![X29, X30]:(~r2_hidden(X29,X30)|~r1_tarski(X30,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.40  cnf(c_0_29, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.40  cnf(c_0_30, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.40  fof(c_0_31, plain, ![X31, X32, X33, X34]:((((r2_hidden(u1_struct_0(X31),u1_pre_topc(X31))|~v2_pre_topc(X31)|~l1_pre_topc(X31))&(~m1_subset_1(X32,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X31))))|(~r1_tarski(X32,u1_pre_topc(X31))|r2_hidden(k5_setfam_1(u1_struct_0(X31),X32),u1_pre_topc(X31)))|~v2_pre_topc(X31)|~l1_pre_topc(X31)))&(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X31)))|(~r2_hidden(X33,u1_pre_topc(X31))|~r2_hidden(X34,u1_pre_topc(X31))|r2_hidden(k9_subset_1(u1_struct_0(X31),X33,X34),u1_pre_topc(X31))))|~v2_pre_topc(X31)|~l1_pre_topc(X31)))&(((m1_subset_1(esk4_1(X31),k1_zfmisc_1(u1_struct_0(X31)))|(m1_subset_1(esk3_1(X31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X31))))|~r2_hidden(u1_struct_0(X31),u1_pre_topc(X31)))|v2_pre_topc(X31)|~l1_pre_topc(X31))&((m1_subset_1(esk5_1(X31),k1_zfmisc_1(u1_struct_0(X31)))|(m1_subset_1(esk3_1(X31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X31))))|~r2_hidden(u1_struct_0(X31),u1_pre_topc(X31)))|v2_pre_topc(X31)|~l1_pre_topc(X31))&(((r2_hidden(esk4_1(X31),u1_pre_topc(X31))|(m1_subset_1(esk3_1(X31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X31))))|~r2_hidden(u1_struct_0(X31),u1_pre_topc(X31)))|v2_pre_topc(X31)|~l1_pre_topc(X31))&(r2_hidden(esk5_1(X31),u1_pre_topc(X31))|(m1_subset_1(esk3_1(X31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X31))))|~r2_hidden(u1_struct_0(X31),u1_pre_topc(X31)))|v2_pre_topc(X31)|~l1_pre_topc(X31)))&(~r2_hidden(k9_subset_1(u1_struct_0(X31),esk4_1(X31),esk5_1(X31)),u1_pre_topc(X31))|(m1_subset_1(esk3_1(X31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X31))))|~r2_hidden(u1_struct_0(X31),u1_pre_topc(X31)))|v2_pre_topc(X31)|~l1_pre_topc(X31)))))&(((m1_subset_1(esk4_1(X31),k1_zfmisc_1(u1_struct_0(X31)))|(r1_tarski(esk3_1(X31),u1_pre_topc(X31))|~r2_hidden(u1_struct_0(X31),u1_pre_topc(X31)))|v2_pre_topc(X31)|~l1_pre_topc(X31))&((m1_subset_1(esk5_1(X31),k1_zfmisc_1(u1_struct_0(X31)))|(r1_tarski(esk3_1(X31),u1_pre_topc(X31))|~r2_hidden(u1_struct_0(X31),u1_pre_topc(X31)))|v2_pre_topc(X31)|~l1_pre_topc(X31))&(((r2_hidden(esk4_1(X31),u1_pre_topc(X31))|(r1_tarski(esk3_1(X31),u1_pre_topc(X31))|~r2_hidden(u1_struct_0(X31),u1_pre_topc(X31)))|v2_pre_topc(X31)|~l1_pre_topc(X31))&(r2_hidden(esk5_1(X31),u1_pre_topc(X31))|(r1_tarski(esk3_1(X31),u1_pre_topc(X31))|~r2_hidden(u1_struct_0(X31),u1_pre_topc(X31)))|v2_pre_topc(X31)|~l1_pre_topc(X31)))&(~r2_hidden(k9_subset_1(u1_struct_0(X31),esk4_1(X31),esk5_1(X31)),u1_pre_topc(X31))|(r1_tarski(esk3_1(X31),u1_pre_topc(X31))|~r2_hidden(u1_struct_0(X31),u1_pre_topc(X31)))|v2_pre_topc(X31)|~l1_pre_topc(X31)))))&((m1_subset_1(esk4_1(X31),k1_zfmisc_1(u1_struct_0(X31)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X31),esk3_1(X31)),u1_pre_topc(X31))|~r2_hidden(u1_struct_0(X31),u1_pre_topc(X31)))|v2_pre_topc(X31)|~l1_pre_topc(X31))&((m1_subset_1(esk5_1(X31),k1_zfmisc_1(u1_struct_0(X31)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X31),esk3_1(X31)),u1_pre_topc(X31))|~r2_hidden(u1_struct_0(X31),u1_pre_topc(X31)))|v2_pre_topc(X31)|~l1_pre_topc(X31))&(((r2_hidden(esk4_1(X31),u1_pre_topc(X31))|(~r2_hidden(k5_setfam_1(u1_struct_0(X31),esk3_1(X31)),u1_pre_topc(X31))|~r2_hidden(u1_struct_0(X31),u1_pre_topc(X31)))|v2_pre_topc(X31)|~l1_pre_topc(X31))&(r2_hidden(esk5_1(X31),u1_pre_topc(X31))|(~r2_hidden(k5_setfam_1(u1_struct_0(X31),esk3_1(X31)),u1_pre_topc(X31))|~r2_hidden(u1_struct_0(X31),u1_pre_topc(X31)))|v2_pre_topc(X31)|~l1_pre_topc(X31)))&(~r2_hidden(k9_subset_1(u1_struct_0(X31),esk4_1(X31),esk5_1(X31)),u1_pre_topc(X31))|(~r2_hidden(k5_setfam_1(u1_struct_0(X31),esk3_1(X31)),u1_pre_topc(X31))|~r2_hidden(u1_struct_0(X31),u1_pre_topc(X31)))|v2_pre_topc(X31)|~l1_pre_topc(X31)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.19/0.40  cnf(c_0_32, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r2_hidden(X2,u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.40  cnf(c_0_33, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.40  fof(c_0_34, negated_conjecture, (((~v2_struct_0(esk6_0)&v2_pre_topc(esk6_0))&l1_pre_topc(esk6_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk6_0)))!=u1_struct_0(esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_27])])])])).
% 0.19/0.40  cnf(c_0_35, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_36, plain, (r1_tarski(k3_tarski(X1),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.40  cnf(c_0_37, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.40  cnf(c_0_38, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|v1_xboole_0(u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.40  cnf(c_0_39, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_40, plain, (~r2_hidden(X1,k3_tarski(X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.40  fof(c_0_41, plain, ![X16]:k3_tarski(k1_zfmisc_1(X16))=X16, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.19/0.40  cnf(c_0_42, plain, (~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_29, c_0_37])).
% 0.19/0.40  cnf(c_0_43, negated_conjecture, (r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk6_0)))|v1_xboole_0(u1_pre_topc(esk6_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_45, plain, (v1_xboole_0(k3_tarski(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_40, c_0_33])).
% 0.19/0.40  cnf(c_0_46, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_39])])).
% 0.19/0.40  cnf(c_0_48, plain, (v1_xboole_0(X1)|~v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.40  cnf(c_0_49, negated_conjecture, (~v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_29, c_0_47])).
% 0.19/0.40  cnf(c_0_50, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_48, c_0_26])).
% 0.19/0.40  fof(c_0_51, plain, ![X23, X24, X25]:(~r1_tarski(k3_tarski(X23),X24)|~r2_hidden(X25,X23)|r1_tarski(X25,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).
% 0.19/0.40  cnf(c_0_52, negated_conjecture, (r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.40  cnf(c_0_53, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_tarski(X1),X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.40  cnf(c_0_54, plain, (r2_hidden(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_21, c_0_20])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (~v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))), inference(spm,[status(thm)],[c_0_29, c_0_52])).
% 0.19/0.40  fof(c_0_56, plain, ![X14, X15]:(~r1_tarski(X14,X15)|r1_tarski(k3_tarski(X14),k3_tarski(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.19/0.40  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_53, c_0_46])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, (r2_hidden(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_39]), c_0_55])).
% 0.19/0.40  fof(c_0_59, plain, ![X10]:r1_tarski(X10,k1_zfmisc_1(k3_tarski(X10))), inference(variable_rename,[status(thm)],[t100_zfmisc_1])).
% 0.19/0.40  cnf(c_0_60, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.40  cnf(c_0_61, negated_conjecture, (r1_tarski(u1_pre_topc(esk6_0),X1)|~r1_tarski(k1_zfmisc_1(u1_struct_0(esk6_0)),X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.40  cnf(c_0_62, plain, (r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.40  cnf(c_0_63, plain, (r1_tarski(X1,k3_tarski(X2))|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_53, c_0_60])).
% 0.19/0.40  cnf(c_0_64, negated_conjecture, (r1_tarski(u1_pre_topc(esk6_0),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_46])).
% 0.19/0.40  cnf(c_0_65, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.40  cnf(c_0_66, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk6_0))|~r2_hidden(X1,u1_pre_topc(esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_46])).
% 0.19/0.40  fof(c_0_67, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.40  cnf(c_0_68, negated_conjecture, (r1_tarski(k3_tarski(X1),u1_struct_0(esk6_0))|~r2_hidden(esk2_2(X1,u1_struct_0(esk6_0)),u1_pre_topc(esk6_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.40  cnf(c_0_69, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.40  fof(c_0_70, plain, ![X39]:(v1_xboole_0(X39)|(~r2_hidden(k3_tarski(X39),X39)|k4_yellow_0(k2_yellow_1(X39))=k3_tarski(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.19/0.40  cnf(c_0_71, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.40  cnf(c_0_72, negated_conjecture, (r1_tarski(k3_tarski(u1_pre_topc(esk6_0)),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_68, c_0_30])).
% 0.19/0.40  cnf(c_0_73, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_69])).
% 0.19/0.40  cnf(c_0_74, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.40  cnf(c_0_75, negated_conjecture, (k3_tarski(u1_pre_topc(esk6_0))=u1_struct_0(esk6_0)|~r1_tarski(u1_struct_0(esk6_0),k3_tarski(u1_pre_topc(esk6_0)))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.19/0.40  cnf(c_0_76, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_53, c_0_73])).
% 0.19/0.40  cnf(c_0_77, plain, (k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(csr,[status(thm)],[c_0_74, c_0_29])).
% 0.19/0.40  cnf(c_0_78, negated_conjecture, (k3_tarski(u1_pre_topc(esk6_0))=u1_struct_0(esk6_0)|~r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.40  cnf(c_0_79, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk6_0)))!=u1_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_80, negated_conjecture, (~r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])).
% 0.19/0.40  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_37]), c_0_44]), c_0_39])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 82
% 0.19/0.40  # Proof object clause steps            : 51
% 0.19/0.40  # Proof object formula steps           : 31
% 0.19/0.40  # Proof object conjectures             : 21
% 0.19/0.40  # Proof object clause conjectures      : 18
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 20
% 0.19/0.40  # Proof object initial formulas used   : 15
% 0.19/0.40  # Proof object generating inferences   : 29
% 0.19/0.40  # Proof object simplifying inferences  : 12
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 16
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 40
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 40
% 0.19/0.40  # Processed clauses                    : 459
% 0.19/0.40  # ...of these trivial                  : 6
% 0.19/0.40  # ...subsumed                          : 192
% 0.19/0.40  # ...remaining for further processing  : 261
% 0.19/0.40  # Other redundant clauses eliminated   : 2
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 1
% 0.19/0.40  # Backward-rewritten                   : 5
% 0.19/0.40  # Generated clauses                    : 1212
% 0.19/0.40  # ...of the previous two non-trivial   : 1036
% 0.19/0.40  # Contextual simplify-reflections      : 2
% 0.19/0.40  # Paramodulations                      : 1210
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 2
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 214
% 0.19/0.40  #    Positive orientable unit clauses  : 19
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 20
% 0.19/0.40  #    Non-unit-clauses                  : 175
% 0.19/0.40  # Current number of unprocessed clauses: 647
% 0.19/0.40  # ...number of literals in the above   : 1831
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 45
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 5092
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 2503
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 108
% 0.19/0.40  # Unit Clause-clause subsumption calls : 232
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 10
% 0.19/0.40  # BW rewrite match successes           : 4
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 16571
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.056 s
% 0.19/0.40  # System time              : 0.005 s
% 0.19/0.40  # Total time               : 0.061 s
% 0.19/0.40  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
