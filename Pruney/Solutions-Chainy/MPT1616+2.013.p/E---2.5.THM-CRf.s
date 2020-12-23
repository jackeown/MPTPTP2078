%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:58 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 146 expanded)
%              Number of clauses        :   48 (  67 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :   19
%              Number of atoms          :  295 ( 588 expanded)
%              Number of equality atoms :   27 (  60 expanded)
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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t24_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

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

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(t56_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(k3_tarski(X1),X2)
        & r2_hidden(X3,X1) )
     => r1_tarski(X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

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

fof(c_0_14,plain,(
    ! [X35,X36,X37] :
      ( ~ r2_hidden(X35,X36)
      | ~ m1_subset_1(X36,k1_zfmisc_1(X37))
      | ~ v1_xboole_0(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_15,plain,(
    ! [X47] :
      ( ~ l1_pre_topc(X47)
      | m1_subset_1(u1_pre_topc(X47),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X47)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_16,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X27,X28)
      | v1_xboole_0(X28)
      | r2_hidden(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_17,plain,(
    ! [X26] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X26)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_18,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_19,plain,(
    ! [X22,X23] :
      ( ( r2_hidden(esk5_2(X22,X23),X22)
        | r1_tarski(k3_tarski(X22),X23) )
      & ( ~ r1_tarski(esk5_2(X22,X23),X23)
        | r1_tarski(k3_tarski(X22),X23) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X38,X39] :
      ( ~ r2_hidden(X38,X39)
      | ~ r1_tarski(X39,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_25,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_32,plain,(
    ! [X25] : k3_tarski(k1_zfmisc_1(X25)) = X25 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

fof(c_0_33,plain,(
    ! [X40,X41,X42,X43] :
      ( ( r2_hidden(u1_struct_0(X40),u1_pre_topc(X40))
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( ~ m1_subset_1(X41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X40))))
        | ~ r1_tarski(X41,u1_pre_topc(X40))
        | r2_hidden(k5_setfam_1(u1_struct_0(X40),X41),u1_pre_topc(X40))
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ r2_hidden(X42,u1_pre_topc(X40))
        | ~ r2_hidden(X43,u1_pre_topc(X40))
        | r2_hidden(k9_subset_1(u1_struct_0(X40),X42,X43),u1_pre_topc(X40))
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( m1_subset_1(esk7_1(X40),k1_zfmisc_1(u1_struct_0(X40)))
        | m1_subset_1(esk6_1(X40),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X40))))
        | ~ r2_hidden(u1_struct_0(X40),u1_pre_topc(X40))
        | v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( m1_subset_1(esk8_1(X40),k1_zfmisc_1(u1_struct_0(X40)))
        | m1_subset_1(esk6_1(X40),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X40))))
        | ~ r2_hidden(u1_struct_0(X40),u1_pre_topc(X40))
        | v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( r2_hidden(esk7_1(X40),u1_pre_topc(X40))
        | m1_subset_1(esk6_1(X40),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X40))))
        | ~ r2_hidden(u1_struct_0(X40),u1_pre_topc(X40))
        | v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( r2_hidden(esk8_1(X40),u1_pre_topc(X40))
        | m1_subset_1(esk6_1(X40),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X40))))
        | ~ r2_hidden(u1_struct_0(X40),u1_pre_topc(X40))
        | v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X40),esk7_1(X40),esk8_1(X40)),u1_pre_topc(X40))
        | m1_subset_1(esk6_1(X40),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X40))))
        | ~ r2_hidden(u1_struct_0(X40),u1_pre_topc(X40))
        | v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( m1_subset_1(esk7_1(X40),k1_zfmisc_1(u1_struct_0(X40)))
        | r1_tarski(esk6_1(X40),u1_pre_topc(X40))
        | ~ r2_hidden(u1_struct_0(X40),u1_pre_topc(X40))
        | v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( m1_subset_1(esk8_1(X40),k1_zfmisc_1(u1_struct_0(X40)))
        | r1_tarski(esk6_1(X40),u1_pre_topc(X40))
        | ~ r2_hidden(u1_struct_0(X40),u1_pre_topc(X40))
        | v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( r2_hidden(esk7_1(X40),u1_pre_topc(X40))
        | r1_tarski(esk6_1(X40),u1_pre_topc(X40))
        | ~ r2_hidden(u1_struct_0(X40),u1_pre_topc(X40))
        | v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( r2_hidden(esk8_1(X40),u1_pre_topc(X40))
        | r1_tarski(esk6_1(X40),u1_pre_topc(X40))
        | ~ r2_hidden(u1_struct_0(X40),u1_pre_topc(X40))
        | v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X40),esk7_1(X40),esk8_1(X40)),u1_pre_topc(X40))
        | r1_tarski(esk6_1(X40),u1_pre_topc(X40))
        | ~ r2_hidden(u1_struct_0(X40),u1_pre_topc(X40))
        | v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( m1_subset_1(esk7_1(X40),k1_zfmisc_1(u1_struct_0(X40)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X40),esk6_1(X40)),u1_pre_topc(X40))
        | ~ r2_hidden(u1_struct_0(X40),u1_pre_topc(X40))
        | v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( m1_subset_1(esk8_1(X40),k1_zfmisc_1(u1_struct_0(X40)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X40),esk6_1(X40)),u1_pre_topc(X40))
        | ~ r2_hidden(u1_struct_0(X40),u1_pre_topc(X40))
        | v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( r2_hidden(esk7_1(X40),u1_pre_topc(X40))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X40),esk6_1(X40)),u1_pre_topc(X40))
        | ~ r2_hidden(u1_struct_0(X40),u1_pre_topc(X40))
        | v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( r2_hidden(esk8_1(X40),u1_pre_topc(X40))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X40),esk6_1(X40)),u1_pre_topc(X40))
        | ~ r2_hidden(u1_struct_0(X40),u1_pre_topc(X40))
        | v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X40),esk7_1(X40),esk8_1(X40)),u1_pre_topc(X40))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X40),esk6_1(X40)),u1_pre_topc(X40))
        | ~ r2_hidden(u1_struct_0(X40),u1_pre_topc(X40))
        | v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_34,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk9_0)
    & v2_pre_topc(esk9_0)
    & l1_pre_topc(esk9_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk9_0))) != u1_struct_0(esk9_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_29])])])])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k3_tarski(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk9_0)))
    | v1_xboole_0(u1_pre_topc(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( v2_pre_topc(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_41])])).

fof(c_0_48,plain,(
    ! [X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( r2_hidden(X13,esk2_3(X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k3_tarski(X11) )
      & ( r2_hidden(esk2_3(X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k3_tarski(X11) )
      & ( ~ r2_hidden(X15,X16)
        | ~ r2_hidden(X16,X11)
        | r2_hidden(X15,X12)
        | X12 != k3_tarski(X11) )
      & ( ~ r2_hidden(esk3_2(X17,X18),X18)
        | ~ r2_hidden(esk3_2(X17,X18),X20)
        | ~ r2_hidden(X20,X17)
        | X18 = k3_tarski(X17) )
      & ( r2_hidden(esk3_2(X17,X18),esk4_2(X17,X18))
        | r2_hidden(esk3_2(X17,X18),X18)
        | X18 = k3_tarski(X17) )
      & ( r2_hidden(esk4_2(X17,X18),X17)
        | r2_hidden(esk3_2(X17,X18),X18)
        | X18 = k3_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_50,plain,(
    ! [X32,X33,X34] :
      ( ~ r1_tarski(k3_tarski(X32),X33)
      | ~ r2_hidden(X34,X32)
      | r1_tarski(X34,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,plain,
    ( r2_hidden(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_49])).

cnf(c_0_54,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_tarski(X1),X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(u1_pre_topc(esk9_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk9_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_41]),c_0_53])).

fof(c_0_57,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_38])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk9_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk9_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_38])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(u1_struct_0(esk9_0),X2)
    | ~ r2_hidden(X1,u1_pre_topc(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_63,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk5_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk9_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k3_tarski(X1),u1_struct_0(esk9_0))
    | ~ r2_hidden(esk5_2(X1,u1_struct_0(esk9_0)),u1_pre_topc(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_66,plain,(
    ! [X48] :
      ( v1_xboole_0(X48)
      | ~ r2_hidden(k3_tarski(X48),X48)
      | k4_yellow_0(k2_yellow_1(X48)) = k3_tarski(X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

cnf(c_0_67,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k3_tarski(u1_pre_topc(esk9_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_26])).

cnf(c_0_69,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk9_0)) = u1_struct_0(esk9_0)
    | ~ r1_tarski(u1_struct_0(esk9_0),k3_tarski(u1_pre_topc(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_62])).

cnf(c_0_72,plain,
    ( k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(csr,[status(thm)],[c_0_69,c_0_25])).

cnf(c_0_73,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk9_0)) = u1_struct_0(esk9_0)
    | ~ r2_hidden(u1_struct_0(esk9_0),u1_pre_topc(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk9_0))) != u1_struct_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_hidden(u1_struct_0(esk9_0),u1_pre_topc(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_39]),c_0_45]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:41:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.029 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.41  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.19/0.41  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.41  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.41  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.19/0.41  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.41  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_1)).
% 0.19/0.41  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.19/0.41  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.19/0.41  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 0.19/0.41  fof(t56_setfam_1, axiom, ![X1, X2, X3]:((r1_tarski(k3_tarski(X1),X2)&r2_hidden(X3,X1))=>r1_tarski(X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_setfam_1)).
% 0.19/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.41  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.19/0.41  fof(c_0_14, plain, ![X35, X36, X37]:(~r2_hidden(X35,X36)|~m1_subset_1(X36,k1_zfmisc_1(X37))|~v1_xboole_0(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.41  fof(c_0_15, plain, ![X47]:(~l1_pre_topc(X47)|m1_subset_1(u1_pre_topc(X47),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X47))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.19/0.41  fof(c_0_16, plain, ![X27, X28]:(~m1_subset_1(X27,X28)|(v1_xboole_0(X28)|r2_hidden(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.41  fof(c_0_17, plain, ![X26]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X26)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.41  fof(c_0_18, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.41  fof(c_0_19, plain, ![X22, X23]:((r2_hidden(esk5_2(X22,X23),X22)|r1_tarski(k3_tarski(X22),X23))&(~r1_tarski(esk5_2(X22,X23),X23)|r1_tarski(k3_tarski(X22),X23))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.19/0.41  cnf(c_0_20, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_21, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.41  cnf(c_0_22, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_23, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  fof(c_0_24, plain, ![X38, X39]:(~r2_hidden(X38,X39)|~r1_tarski(X39,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.41  cnf(c_0_25, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_26, plain, (r2_hidden(esk5_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_27, plain, (~l1_pre_topc(X1)|~r2_hidden(X2,u1_pre_topc(X1))|~v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.41  cnf(c_0_28, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))|v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.41  fof(c_0_29, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 0.19/0.41  cnf(c_0_30, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.41  cnf(c_0_31, plain, (r1_tarski(k3_tarski(X1),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.41  fof(c_0_32, plain, ![X25]:k3_tarski(k1_zfmisc_1(X25))=X25, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.19/0.41  fof(c_0_33, plain, ![X40, X41, X42, X43]:((((r2_hidden(u1_struct_0(X40),u1_pre_topc(X40))|~v2_pre_topc(X40)|~l1_pre_topc(X40))&(~m1_subset_1(X41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X40))))|(~r1_tarski(X41,u1_pre_topc(X40))|r2_hidden(k5_setfam_1(u1_struct_0(X40),X41),u1_pre_topc(X40)))|~v2_pre_topc(X40)|~l1_pre_topc(X40)))&(~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))|(~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X40)))|(~r2_hidden(X42,u1_pre_topc(X40))|~r2_hidden(X43,u1_pre_topc(X40))|r2_hidden(k9_subset_1(u1_struct_0(X40),X42,X43),u1_pre_topc(X40))))|~v2_pre_topc(X40)|~l1_pre_topc(X40)))&(((m1_subset_1(esk7_1(X40),k1_zfmisc_1(u1_struct_0(X40)))|(m1_subset_1(esk6_1(X40),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X40))))|~r2_hidden(u1_struct_0(X40),u1_pre_topc(X40)))|v2_pre_topc(X40)|~l1_pre_topc(X40))&((m1_subset_1(esk8_1(X40),k1_zfmisc_1(u1_struct_0(X40)))|(m1_subset_1(esk6_1(X40),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X40))))|~r2_hidden(u1_struct_0(X40),u1_pre_topc(X40)))|v2_pre_topc(X40)|~l1_pre_topc(X40))&(((r2_hidden(esk7_1(X40),u1_pre_topc(X40))|(m1_subset_1(esk6_1(X40),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X40))))|~r2_hidden(u1_struct_0(X40),u1_pre_topc(X40)))|v2_pre_topc(X40)|~l1_pre_topc(X40))&(r2_hidden(esk8_1(X40),u1_pre_topc(X40))|(m1_subset_1(esk6_1(X40),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X40))))|~r2_hidden(u1_struct_0(X40),u1_pre_topc(X40)))|v2_pre_topc(X40)|~l1_pre_topc(X40)))&(~r2_hidden(k9_subset_1(u1_struct_0(X40),esk7_1(X40),esk8_1(X40)),u1_pre_topc(X40))|(m1_subset_1(esk6_1(X40),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X40))))|~r2_hidden(u1_struct_0(X40),u1_pre_topc(X40)))|v2_pre_topc(X40)|~l1_pre_topc(X40)))))&(((m1_subset_1(esk7_1(X40),k1_zfmisc_1(u1_struct_0(X40)))|(r1_tarski(esk6_1(X40),u1_pre_topc(X40))|~r2_hidden(u1_struct_0(X40),u1_pre_topc(X40)))|v2_pre_topc(X40)|~l1_pre_topc(X40))&((m1_subset_1(esk8_1(X40),k1_zfmisc_1(u1_struct_0(X40)))|(r1_tarski(esk6_1(X40),u1_pre_topc(X40))|~r2_hidden(u1_struct_0(X40),u1_pre_topc(X40)))|v2_pre_topc(X40)|~l1_pre_topc(X40))&(((r2_hidden(esk7_1(X40),u1_pre_topc(X40))|(r1_tarski(esk6_1(X40),u1_pre_topc(X40))|~r2_hidden(u1_struct_0(X40),u1_pre_topc(X40)))|v2_pre_topc(X40)|~l1_pre_topc(X40))&(r2_hidden(esk8_1(X40),u1_pre_topc(X40))|(r1_tarski(esk6_1(X40),u1_pre_topc(X40))|~r2_hidden(u1_struct_0(X40),u1_pre_topc(X40)))|v2_pre_topc(X40)|~l1_pre_topc(X40)))&(~r2_hidden(k9_subset_1(u1_struct_0(X40),esk7_1(X40),esk8_1(X40)),u1_pre_topc(X40))|(r1_tarski(esk6_1(X40),u1_pre_topc(X40))|~r2_hidden(u1_struct_0(X40),u1_pre_topc(X40)))|v2_pre_topc(X40)|~l1_pre_topc(X40)))))&((m1_subset_1(esk7_1(X40),k1_zfmisc_1(u1_struct_0(X40)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X40),esk6_1(X40)),u1_pre_topc(X40))|~r2_hidden(u1_struct_0(X40),u1_pre_topc(X40)))|v2_pre_topc(X40)|~l1_pre_topc(X40))&((m1_subset_1(esk8_1(X40),k1_zfmisc_1(u1_struct_0(X40)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X40),esk6_1(X40)),u1_pre_topc(X40))|~r2_hidden(u1_struct_0(X40),u1_pre_topc(X40)))|v2_pre_topc(X40)|~l1_pre_topc(X40))&(((r2_hidden(esk7_1(X40),u1_pre_topc(X40))|(~r2_hidden(k5_setfam_1(u1_struct_0(X40),esk6_1(X40)),u1_pre_topc(X40))|~r2_hidden(u1_struct_0(X40),u1_pre_topc(X40)))|v2_pre_topc(X40)|~l1_pre_topc(X40))&(r2_hidden(esk8_1(X40),u1_pre_topc(X40))|(~r2_hidden(k5_setfam_1(u1_struct_0(X40),esk6_1(X40)),u1_pre_topc(X40))|~r2_hidden(u1_struct_0(X40),u1_pre_topc(X40)))|v2_pre_topc(X40)|~l1_pre_topc(X40)))&(~r2_hidden(k9_subset_1(u1_struct_0(X40),esk7_1(X40),esk8_1(X40)),u1_pre_topc(X40))|(~r2_hidden(k5_setfam_1(u1_struct_0(X40),esk6_1(X40)),u1_pre_topc(X40))|~r2_hidden(u1_struct_0(X40),u1_pre_topc(X40)))|v2_pre_topc(X40)|~l1_pre_topc(X40)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.19/0.41  cnf(c_0_34, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r2_hidden(X2,u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.41  cnf(c_0_35, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  fof(c_0_36, negated_conjecture, (((~v2_struct_0(esk9_0)&v2_pre_topc(esk9_0))&l1_pre_topc(esk9_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk9_0)))!=u1_struct_0(esk9_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_29])])])])).
% 0.19/0.41  cnf(c_0_37, plain, (~r2_hidden(X1,k3_tarski(X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.41  cnf(c_0_38, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.41  cnf(c_0_39, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.41  cnf(c_0_40, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|v1_xboole_0(u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (l1_pre_topc(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_42, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.41  cnf(c_0_43, plain, (~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_25, c_0_39])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk9_0)))|v1_xboole_0(u1_pre_topc(esk9_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.41  cnf(c_0_45, negated_conjecture, (v2_pre_topc(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_46, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_28])).
% 0.19/0.41  cnf(c_0_47, negated_conjecture, (r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk9_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_41])])).
% 0.19/0.41  fof(c_0_48, plain, ![X11, X12, X13, X15, X16, X17, X18, X20]:((((r2_hidden(X13,esk2_3(X11,X12,X13))|~r2_hidden(X13,X12)|X12!=k3_tarski(X11))&(r2_hidden(esk2_3(X11,X12,X13),X11)|~r2_hidden(X13,X12)|X12!=k3_tarski(X11)))&(~r2_hidden(X15,X16)|~r2_hidden(X16,X11)|r2_hidden(X15,X12)|X12!=k3_tarski(X11)))&((~r2_hidden(esk3_2(X17,X18),X18)|(~r2_hidden(esk3_2(X17,X18),X20)|~r2_hidden(X20,X17))|X18=k3_tarski(X17))&((r2_hidden(esk3_2(X17,X18),esk4_2(X17,X18))|r2_hidden(esk3_2(X17,X18),X18)|X18=k3_tarski(X17))&(r2_hidden(esk4_2(X17,X18),X17)|r2_hidden(esk3_2(X17,X18),X18)|X18=k3_tarski(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.19/0.41  cnf(c_0_49, negated_conjecture, (r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk9_0))))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.41  fof(c_0_50, plain, ![X32, X33, X34]:(~r1_tarski(k3_tarski(X32),X33)|~r2_hidden(X34,X32)|r1_tarski(X34,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).
% 0.19/0.41  cnf(c_0_51, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.41  cnf(c_0_52, plain, (r2_hidden(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.19/0.41  cnf(c_0_53, negated_conjecture, (~v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk9_0))))), inference(spm,[status(thm)],[c_0_25, c_0_49])).
% 0.19/0.41  cnf(c_0_54, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_tarski(X1),X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.41  cnf(c_0_55, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_51])).
% 0.19/0.41  cnf(c_0_56, negated_conjecture, (r2_hidden(u1_pre_topc(esk9_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk9_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_41]), c_0_53])).
% 0.19/0.41  fof(c_0_57, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.41  cnf(c_0_58, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_54, c_0_38])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk9_0)))|~r2_hidden(X1,u1_pre_topc(esk9_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_38])).
% 0.19/0.41  cnf(c_0_60, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(u1_struct_0(esk9_0),X2)|~r2_hidden(X1,u1_pre_topc(esk9_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.41  cnf(c_0_62, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_60])).
% 0.19/0.41  cnf(c_0_63, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk5_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_64, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk9_0))|~r2_hidden(X1,u1_pre_topc(esk9_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.41  cnf(c_0_65, negated_conjecture, (r1_tarski(k3_tarski(X1),u1_struct_0(esk9_0))|~r2_hidden(esk5_2(X1,u1_struct_0(esk9_0)),u1_pre_topc(esk9_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.41  fof(c_0_66, plain, ![X48]:(v1_xboole_0(X48)|(~r2_hidden(k3_tarski(X48),X48)|k4_yellow_0(k2_yellow_1(X48))=k3_tarski(X48))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.19/0.41  cnf(c_0_67, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.41  cnf(c_0_68, negated_conjecture, (r1_tarski(k3_tarski(u1_pre_topc(esk9_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_65, c_0_26])).
% 0.19/0.41  cnf(c_0_69, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.41  cnf(c_0_70, negated_conjecture, (k3_tarski(u1_pre_topc(esk9_0))=u1_struct_0(esk9_0)|~r1_tarski(u1_struct_0(esk9_0),k3_tarski(u1_pre_topc(esk9_0)))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.41  cnf(c_0_71, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_54, c_0_62])).
% 0.19/0.41  cnf(c_0_72, plain, (k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(csr,[status(thm)],[c_0_69, c_0_25])).
% 0.19/0.41  cnf(c_0_73, negated_conjecture, (k3_tarski(u1_pre_topc(esk9_0))=u1_struct_0(esk9_0)|~r2_hidden(u1_struct_0(esk9_0),u1_pre_topc(esk9_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.41  cnf(c_0_74, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk9_0)))!=u1_struct_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_75, negated_conjecture, (~r2_hidden(u1_struct_0(esk9_0),u1_pre_topc(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])).
% 0.19/0.41  cnf(c_0_76, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_39]), c_0_45]), c_0_41])]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 77
% 0.19/0.41  # Proof object clause steps            : 48
% 0.19/0.41  # Proof object formula steps           : 29
% 0.19/0.41  # Proof object conjectures             : 20
% 0.19/0.41  # Proof object clause conjectures      : 17
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 19
% 0.19/0.41  # Proof object initial formulas used   : 14
% 0.19/0.41  # Proof object generating inferences   : 26
% 0.19/0.41  # Proof object simplifying inferences  : 12
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 15
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 44
% 0.19/0.41  # Removed in clause preprocessing      : 0
% 0.19/0.41  # Initial clauses in saturation        : 44
% 0.19/0.41  # Processed clauses                    : 564
% 0.19/0.41  # ...of these trivial                  : 8
% 0.19/0.41  # ...subsumed                          : 279
% 0.19/0.41  # ...remaining for further processing  : 277
% 0.19/0.41  # Other redundant clauses eliminated   : 5
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 1
% 0.19/0.41  # Backward-rewritten                   : 18
% 0.19/0.41  # Generated clauses                    : 1972
% 0.19/0.41  # ...of the previous two non-trivial   : 1815
% 0.19/0.41  # Contextual simplify-reflections      : 2
% 0.19/0.41  # Paramodulations                      : 1967
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 5
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 210
% 0.19/0.41  #    Positive orientable unit clauses  : 17
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 15
% 0.19/0.41  #    Non-unit-clauses                  : 178
% 0.19/0.41  # Current number of unprocessed clauses: 1313
% 0.19/0.41  # ...number of literals in the above   : 4434
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 62
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 7678
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 3287
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 128
% 0.19/0.41  # Unit Clause-clause subsumption calls : 735
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 15
% 0.19/0.41  # BW rewrite match successes           : 6
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 26755
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.065 s
% 0.19/0.41  # System time              : 0.005 s
% 0.19/0.41  # Total time               : 0.070 s
% 0.19/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
