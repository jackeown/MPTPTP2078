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
% DateTime   : Thu Dec  3 11:14:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 202 expanded)
%              Number of clauses        :   38 (  82 expanded)
%              Number of leaves         :   15 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  179 (1091 expanded)
%              Number of equality atoms :   16 (  97 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ~ ( ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r2_hidden(X4,X3)
                      <=> ( v3_pre_topc(X4,X1)
                          & v4_pre_topc(X4,X1)
                          & r2_hidden(X2,X4) ) ) )
                  & X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(fc10_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v3_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(fc4_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v4_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(rc5_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v2_tops_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc5_tops_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(fc14_tops_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ~ v2_tops_1(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_tops_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ~ ( ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r2_hidden(X4,X3)
                        <=> ( v3_pre_topc(X4,X1)
                            & v4_pre_topc(X4,X1)
                            & r2_hidden(X2,X4) ) ) )
                    & X3 = k1_xboole_0 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t28_connsp_2])).

fof(c_0_16,negated_conjecture,(
    ! [X25] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
      & ( v3_pre_topc(X25,esk2_0)
        | ~ r2_hidden(X25,esk4_0)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(esk2_0))) )
      & ( v4_pre_topc(X25,esk2_0)
        | ~ r2_hidden(X25,esk4_0)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(esk2_0))) )
      & ( r2_hidden(esk3_0,X25)
        | ~ r2_hidden(X25,esk4_0)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(esk2_0))) )
      & ( ~ v3_pre_topc(X25,esk2_0)
        | ~ v4_pre_topc(X25,esk2_0)
        | ~ r2_hidden(esk3_0,X25)
        | r2_hidden(X25,esk4_0)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(esk2_0))) )
      & esk4_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).

fof(c_0_17,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | ~ r1_tarski(X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_18,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_19,plain,(
    ! [X15] :
      ( ~ l1_struct_0(X15)
      | k2_struct_0(X15) = u1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_20,plain,(
    ! [X16] :
      ( ~ l1_pre_topc(X16)
      | l1_struct_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ r2_hidden(esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X18] :
      ( ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | v3_pre_topc(k2_struct_0(X18),X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).

cnf(c_0_26,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X8] : m1_subset_1(k2_subset_1(X8),k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_29,plain,(
    ! [X7] : k2_subset_1(X7) = X7 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ r2_hidden(esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( v3_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X17] :
      ( ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | v4_pre_topc(k2_struct_0(X17),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).

cnf(c_0_37,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk2_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ r2_hidden(esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( v3_pre_topc(u1_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,plain,
    ( v4_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_43,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X11,X12)
      | v1_xboole_0(X12)
      | r2_hidden(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_44,negated_conjecture,
    ( ~ v4_pre_topc(u1_struct_0(esk2_0),esk2_0)
    | ~ r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_41])])).

cnf(c_0_45,plain,
    ( v4_pre_topc(u1_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_33])).

fof(c_0_46,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | X5 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_40]),c_0_41])])).

fof(c_0_50,plain,(
    ! [X19] :
      ( ( m1_subset_1(esk1_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( v2_tops_1(esk1_1(X19),X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[rc5_tops_1])])])])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

fof(c_0_53,plain,(
    ! [X9,X10] :
      ( ~ v1_xboole_0(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_xboole_0(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_54,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk1_1(esk2_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_41])])).

cnf(c_0_58,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_59,plain,(
    ! [X21] :
      ( v2_struct_0(X21)
      | ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | ~ v2_tops_1(k2_struct_0(X21),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_tops_1])])])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(esk1_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tops_1(k2_struct_0(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_62,plain,
    ( v2_tops_1(esk1_1(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( esk1_1(esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_60])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | ~ v2_tops_1(u1_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_33])).

cnf(c_0_65,negated_conjecture,
    ( v2_tops_1(k1_xboole_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_41])])).

cnf(c_0_66,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_55]),c_0_65]),c_0_40]),c_0_41])]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.044 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t28_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 0.20/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.39  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.39  fof(fc10_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v3_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 0.20/0.39  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.39  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.39  fof(fc4_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v4_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 0.20/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.39  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.39  fof(rc5_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v2_tops_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc5_tops_1)).
% 0.20/0.39  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.20/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.39  fof(fc14_tops_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>~(v2_tops_1(k2_struct_0(X1),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_tops_1)).
% 0.20/0.39  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t28_connsp_2])).
% 0.20/0.39  fof(c_0_16, negated_conjecture, ![X25]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))&(((((v3_pre_topc(X25,esk2_0)|~r2_hidden(X25,esk4_0)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(esk2_0))))&(v4_pre_topc(X25,esk2_0)|~r2_hidden(X25,esk4_0)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(esk2_0)))))&(r2_hidden(esk3_0,X25)|~r2_hidden(X25,esk4_0)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(esk2_0)))))&(~v3_pre_topc(X25,esk2_0)|~v4_pre_topc(X25,esk2_0)|~r2_hidden(esk3_0,X25)|r2_hidden(X25,esk4_0)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(esk2_0)))))&esk4_0=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).
% 0.20/0.39  fof(c_0_17, plain, ![X13, X14]:(~r2_hidden(X13,X14)|~r1_tarski(X14,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.39  fof(c_0_18, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.39  fof(c_0_19, plain, ![X15]:(~l1_struct_0(X15)|k2_struct_0(X15)=u1_struct_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.39  fof(c_0_20, plain, ![X16]:(~l1_pre_topc(X16)|l1_struct_0(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.39  cnf(c_0_21, negated_conjecture, (r2_hidden(X1,esk4_0)|~v3_pre_topc(X1,esk2_0)|~v4_pre_topc(X1,esk2_0)|~r2_hidden(esk3_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_22, negated_conjecture, (esk4_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_23, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_24, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  fof(c_0_25, plain, ![X18]:(~v2_pre_topc(X18)|~l1_pre_topc(X18)|v3_pre_topc(k2_struct_0(X18),X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).
% 0.20/0.39  cnf(c_0_26, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  cnf(c_0_27, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  fof(c_0_28, plain, ![X8]:m1_subset_1(k2_subset_1(X8),k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.39  fof(c_0_29, plain, ![X7]:k2_subset_1(X7)=X7, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~v3_pre_topc(X1,esk2_0)|~v4_pre_topc(X1,esk2_0)|~r2_hidden(esk3_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.39  cnf(c_0_31, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.39  cnf(c_0_32, plain, (v3_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_33, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.39  cnf(c_0_34, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_35, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  fof(c_0_36, plain, ![X17]:(~v2_pre_topc(X17)|~l1_pre_topc(X17)|v4_pre_topc(k2_struct_0(X17),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (~v3_pre_topc(X1,esk2_0)|~v4_pre_topc(X1,esk2_0)|~r2_hidden(esk3_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.39  cnf(c_0_38, plain, (v3_pre_topc(u1_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.39  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_42, plain, (v4_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.39  fof(c_0_43, plain, ![X11, X12]:(~m1_subset_1(X11,X12)|(v1_xboole_0(X12)|r2_hidden(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (~v4_pre_topc(u1_struct_0(esk2_0),esk2_0)|~r2_hidden(esk3_0,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), c_0_41])])).
% 0.20/0.39  cnf(c_0_45, plain, (v4_pre_topc(u1_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_42, c_0_33])).
% 0.20/0.39  fof(c_0_46, plain, ![X5]:(~v1_xboole_0(X5)|X5=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.39  cnf(c_0_47, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (~r2_hidden(esk3_0,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_40]), c_0_41])])).
% 0.20/0.39  fof(c_0_50, plain, ![X19]:((m1_subset_1(esk1_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(v2_tops_1(esk1_1(X19),X19)|~l1_pre_topc(X19))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[rc5_tops_1])])])])).
% 0.20/0.39  cnf(c_0_51, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.20/0.39  fof(c_0_53, plain, ![X9, X10]:(~v1_xboole_0(X9)|(~m1_subset_1(X10,k1_zfmisc_1(X9))|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.20/0.39  cnf(c_0_54, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.39  cnf(c_0_56, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.39  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk1_1(esk2_0),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_41])])).
% 0.20/0.39  cnf(c_0_58, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.39  fof(c_0_59, plain, ![X21]:(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|~v2_tops_1(k2_struct_0(X21),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_tops_1])])])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (v1_xboole_0(esk1_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 0.20/0.39  cnf(c_0_61, plain, (v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_tops_1(k2_struct_0(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.39  cnf(c_0_62, plain, (v2_tops_1(esk1_1(X1),X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (esk1_1(esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_60])).
% 0.20/0.39  cnf(c_0_64, plain, (v2_struct_0(X1)|~v2_tops_1(u1_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_61, c_0_33])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (v2_tops_1(k1_xboole_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_41])])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_55]), c_0_65]), c_0_40]), c_0_41])]), c_0_66]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 68
% 0.20/0.39  # Proof object clause steps            : 38
% 0.20/0.39  # Proof object formula steps           : 30
% 0.20/0.39  # Proof object conjectures             : 20
% 0.20/0.39  # Proof object clause conjectures      : 17
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 21
% 0.20/0.39  # Proof object initial formulas used   : 15
% 0.20/0.39  # Proof object generating inferences   : 14
% 0.20/0.39  # Proof object simplifying inferences  : 22
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 15
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 25
% 0.20/0.39  # Removed in clause preprocessing      : 1
% 0.20/0.39  # Initial clauses in saturation        : 24
% 0.20/0.39  # Processed clauses                    : 72
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 7
% 0.20/0.39  # ...remaining for further processing  : 65
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 8
% 0.20/0.39  # Generated clauses                    : 32
% 0.20/0.39  # ...of the previous two non-trivial   : 31
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 32
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
% 0.20/0.39  # Current number of processed clauses  : 33
% 0.20/0.39  #    Positive orientable unit clauses  : 13
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 2
% 0.20/0.39  #    Non-unit-clauses                  : 18
% 0.20/0.39  # Current number of unprocessed clauses: 7
% 0.20/0.39  # ...number of literals in the above   : 18
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 33
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 127
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 85
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.39  # Unit Clause-clause subsumption calls : 2
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 3
% 0.20/0.39  # BW rewrite match successes           : 2
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 2166
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.046 s
% 0.20/0.39  # System time              : 0.007 s
% 0.20/0.39  # Total time               : 0.052 s
% 0.20/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
