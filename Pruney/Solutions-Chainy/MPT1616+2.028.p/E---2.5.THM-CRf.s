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
% DateTime   : Thu Dec  3 11:16:00 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   39 (  51 expanded)
%              Number of clauses        :   20 (  22 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :  196 ( 330 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( m1_setfam_1(X2,X1)
      <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(d12_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_setfam_1(X2,X1)
    <=> r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(t24_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

fof(c_0_9,plain,(
    ! [X14,X15] :
      ( ( ~ m1_setfam_1(X15,X14)
        | k5_setfam_1(X14,X15) = X14
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))) )
      & ( k5_setfam_1(X14,X15) != X14
        | m1_setfam_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).

fof(c_0_10,plain,(
    ! [X23] :
      ( ~ l1_pre_topc(X23)
      | m1_subset_1(u1_pre_topc(X23),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_11,plain,(
    ! [X10,X11] :
      ( ( ~ m1_setfam_1(X11,X10)
        | r1_tarski(X10,k3_tarski(X11)) )
      & ( ~ r1_tarski(X10,k3_tarski(X11))
        | m1_setfam_1(X11,X10) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).

fof(c_0_12,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,X9)
      | r1_tarski(X8,k3_tarski(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_13,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12)))
      | k5_setfam_1(X12,X13) = k3_tarski(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

cnf(c_0_14,plain,
    ( k5_setfam_1(X2,X1) = X2
    | ~ m1_setfam_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( m1_setfam_1(X2,X1)
    | ~ r1_tarski(X1,k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k5_setfam_1(u1_struct_0(X1),u1_pre_topc(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_setfam_1(u1_pre_topc(X1),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( m1_setfam_1(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,plain,(
    ! [X24] :
      ( v1_xboole_0(X24)
      | ~ r2_hidden(k3_tarski(X24),X24)
      | k4_yellow_0(k2_yellow_1(X24)) = k3_tarski(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

fof(c_0_22,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_23,plain,
    ( k5_setfam_1(u1_struct_0(X1),u1_pre_topc(X1)) = k3_tarski(u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_24,plain,
    ( k5_setfam_1(u1_struct_0(X1),u1_pre_topc(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_25,plain,(
    ! [X16,X17,X18,X19] :
      ( ( r2_hidden(u1_struct_0(X16),u1_pre_topc(X16))
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))
        | ~ r1_tarski(X17,u1_pre_topc(X16))
        | r2_hidden(k5_setfam_1(u1_struct_0(X16),X17),u1_pre_topc(X16))
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ r2_hidden(X18,u1_pre_topc(X16))
        | ~ r2_hidden(X19,u1_pre_topc(X16))
        | r2_hidden(k9_subset_1(u1_struct_0(X16),X18,X19),u1_pre_topc(X16))
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk3_1(X16),k1_zfmisc_1(u1_struct_0(X16)))
        | m1_subset_1(esk2_1(X16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))
        | ~ r2_hidden(u1_struct_0(X16),u1_pre_topc(X16))
        | v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk4_1(X16),k1_zfmisc_1(u1_struct_0(X16)))
        | m1_subset_1(esk2_1(X16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))
        | ~ r2_hidden(u1_struct_0(X16),u1_pre_topc(X16))
        | v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( r2_hidden(esk3_1(X16),u1_pre_topc(X16))
        | m1_subset_1(esk2_1(X16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))
        | ~ r2_hidden(u1_struct_0(X16),u1_pre_topc(X16))
        | v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( r2_hidden(esk4_1(X16),u1_pre_topc(X16))
        | m1_subset_1(esk2_1(X16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))
        | ~ r2_hidden(u1_struct_0(X16),u1_pre_topc(X16))
        | v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X16),esk3_1(X16),esk4_1(X16)),u1_pre_topc(X16))
        | m1_subset_1(esk2_1(X16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))
        | ~ r2_hidden(u1_struct_0(X16),u1_pre_topc(X16))
        | v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk3_1(X16),k1_zfmisc_1(u1_struct_0(X16)))
        | r1_tarski(esk2_1(X16),u1_pre_topc(X16))
        | ~ r2_hidden(u1_struct_0(X16),u1_pre_topc(X16))
        | v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk4_1(X16),k1_zfmisc_1(u1_struct_0(X16)))
        | r1_tarski(esk2_1(X16),u1_pre_topc(X16))
        | ~ r2_hidden(u1_struct_0(X16),u1_pre_topc(X16))
        | v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( r2_hidden(esk3_1(X16),u1_pre_topc(X16))
        | r1_tarski(esk2_1(X16),u1_pre_topc(X16))
        | ~ r2_hidden(u1_struct_0(X16),u1_pre_topc(X16))
        | v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( r2_hidden(esk4_1(X16),u1_pre_topc(X16))
        | r1_tarski(esk2_1(X16),u1_pre_topc(X16))
        | ~ r2_hidden(u1_struct_0(X16),u1_pre_topc(X16))
        | v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X16),esk3_1(X16),esk4_1(X16)),u1_pre_topc(X16))
        | r1_tarski(esk2_1(X16),u1_pre_topc(X16))
        | ~ r2_hidden(u1_struct_0(X16),u1_pre_topc(X16))
        | v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk3_1(X16),k1_zfmisc_1(u1_struct_0(X16)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X16),esk2_1(X16)),u1_pre_topc(X16))
        | ~ r2_hidden(u1_struct_0(X16),u1_pre_topc(X16))
        | v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk4_1(X16),k1_zfmisc_1(u1_struct_0(X16)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X16),esk2_1(X16)),u1_pre_topc(X16))
        | ~ r2_hidden(u1_struct_0(X16),u1_pre_topc(X16))
        | v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( r2_hidden(esk3_1(X16),u1_pre_topc(X16))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X16),esk2_1(X16)),u1_pre_topc(X16))
        | ~ r2_hidden(u1_struct_0(X16),u1_pre_topc(X16))
        | v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( r2_hidden(esk4_1(X16),u1_pre_topc(X16))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X16),esk2_1(X16)),u1_pre_topc(X16))
        | ~ r2_hidden(u1_struct_0(X16),u1_pre_topc(X16))
        | v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X16),esk3_1(X16),esk4_1(X16)),u1_pre_topc(X16))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X16),esk2_1(X16)),u1_pre_topc(X16))
        | ~ r2_hidden(u1_struct_0(X16),u1_pre_topc(X16))
        | v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k3_tarski(u1_pre_topc(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk5_0))) != u1_struct_0(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_26])])])])).

cnf(c_0_32,plain,
    ( k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(csr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( k3_tarski(u1_pre_topc(X1)) = u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk5_0))) != u1_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:42:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.39  #
% 0.18/0.39  # Preprocessing time       : 0.048 s
% 0.18/0.39  # Presaturation interreduction done
% 0.18/0.39  
% 0.18/0.39  # Proof found!
% 0.18/0.39  # SZS status Theorem
% 0.18/0.39  # SZS output start CNFRefutation
% 0.18/0.39  fof(t60_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(m1_setfam_1(X2,X1)<=>k5_setfam_1(X1,X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 0.18/0.39  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.18/0.39  fof(d12_setfam_1, axiom, ![X1, X2]:(m1_setfam_1(X2,X1)<=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 0.18/0.39  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.18/0.39  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.18/0.39  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.18/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.18/0.39  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.18/0.39  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_1)).
% 0.18/0.39  fof(c_0_9, plain, ![X14, X15]:((~m1_setfam_1(X15,X14)|k5_setfam_1(X14,X15)=X14|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))))&(k5_setfam_1(X14,X15)!=X14|m1_setfam_1(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).
% 0.18/0.39  fof(c_0_10, plain, ![X23]:(~l1_pre_topc(X23)|m1_subset_1(u1_pre_topc(X23),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.18/0.39  fof(c_0_11, plain, ![X10, X11]:((~m1_setfam_1(X11,X10)|r1_tarski(X10,k3_tarski(X11)))&(~r1_tarski(X10,k3_tarski(X11))|m1_setfam_1(X11,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).
% 0.18/0.39  fof(c_0_12, plain, ![X8, X9]:(~r2_hidden(X8,X9)|r1_tarski(X8,k3_tarski(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.18/0.39  fof(c_0_13, plain, ![X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12)))|k5_setfam_1(X12,X13)=k3_tarski(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.18/0.39  cnf(c_0_14, plain, (k5_setfam_1(X2,X1)=X2|~m1_setfam_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.39  cnf(c_0_15, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  cnf(c_0_16, plain, (m1_setfam_1(X2,X1)|~r1_tarski(X1,k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.39  cnf(c_0_17, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.39  cnf(c_0_18, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.39  cnf(c_0_19, plain, (k5_setfam_1(u1_struct_0(X1),u1_pre_topc(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)|~m1_setfam_1(u1_pre_topc(X1),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.18/0.39  cnf(c_0_20, plain, (m1_setfam_1(X1,X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.39  fof(c_0_21, plain, ![X24]:(v1_xboole_0(X24)|(~r2_hidden(k3_tarski(X24),X24)|k4_yellow_0(k2_yellow_1(X24))=k3_tarski(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.18/0.39  fof(c_0_22, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.18/0.39  cnf(c_0_23, plain, (k5_setfam_1(u1_struct_0(X1),u1_pre_topc(X1))=k3_tarski(u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_18, c_0_15])).
% 0.18/0.39  cnf(c_0_24, plain, (k5_setfam_1(u1_struct_0(X1),u1_pre_topc(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.18/0.39  fof(c_0_25, plain, ![X16, X17, X18, X19]:((((r2_hidden(u1_struct_0(X16),u1_pre_topc(X16))|~v2_pre_topc(X16)|~l1_pre_topc(X16))&(~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))|(~r1_tarski(X17,u1_pre_topc(X16))|r2_hidden(k5_setfam_1(u1_struct_0(X16),X17),u1_pre_topc(X16)))|~v2_pre_topc(X16)|~l1_pre_topc(X16)))&(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))|(~r2_hidden(X18,u1_pre_topc(X16))|~r2_hidden(X19,u1_pre_topc(X16))|r2_hidden(k9_subset_1(u1_struct_0(X16),X18,X19),u1_pre_topc(X16))))|~v2_pre_topc(X16)|~l1_pre_topc(X16)))&(((m1_subset_1(esk3_1(X16),k1_zfmisc_1(u1_struct_0(X16)))|(m1_subset_1(esk2_1(X16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))|~r2_hidden(u1_struct_0(X16),u1_pre_topc(X16)))|v2_pre_topc(X16)|~l1_pre_topc(X16))&((m1_subset_1(esk4_1(X16),k1_zfmisc_1(u1_struct_0(X16)))|(m1_subset_1(esk2_1(X16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))|~r2_hidden(u1_struct_0(X16),u1_pre_topc(X16)))|v2_pre_topc(X16)|~l1_pre_topc(X16))&(((r2_hidden(esk3_1(X16),u1_pre_topc(X16))|(m1_subset_1(esk2_1(X16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))|~r2_hidden(u1_struct_0(X16),u1_pre_topc(X16)))|v2_pre_topc(X16)|~l1_pre_topc(X16))&(r2_hidden(esk4_1(X16),u1_pre_topc(X16))|(m1_subset_1(esk2_1(X16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))|~r2_hidden(u1_struct_0(X16),u1_pre_topc(X16)))|v2_pre_topc(X16)|~l1_pre_topc(X16)))&(~r2_hidden(k9_subset_1(u1_struct_0(X16),esk3_1(X16),esk4_1(X16)),u1_pre_topc(X16))|(m1_subset_1(esk2_1(X16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))|~r2_hidden(u1_struct_0(X16),u1_pre_topc(X16)))|v2_pre_topc(X16)|~l1_pre_topc(X16)))))&(((m1_subset_1(esk3_1(X16),k1_zfmisc_1(u1_struct_0(X16)))|(r1_tarski(esk2_1(X16),u1_pre_topc(X16))|~r2_hidden(u1_struct_0(X16),u1_pre_topc(X16)))|v2_pre_topc(X16)|~l1_pre_topc(X16))&((m1_subset_1(esk4_1(X16),k1_zfmisc_1(u1_struct_0(X16)))|(r1_tarski(esk2_1(X16),u1_pre_topc(X16))|~r2_hidden(u1_struct_0(X16),u1_pre_topc(X16)))|v2_pre_topc(X16)|~l1_pre_topc(X16))&(((r2_hidden(esk3_1(X16),u1_pre_topc(X16))|(r1_tarski(esk2_1(X16),u1_pre_topc(X16))|~r2_hidden(u1_struct_0(X16),u1_pre_topc(X16)))|v2_pre_topc(X16)|~l1_pre_topc(X16))&(r2_hidden(esk4_1(X16),u1_pre_topc(X16))|(r1_tarski(esk2_1(X16),u1_pre_topc(X16))|~r2_hidden(u1_struct_0(X16),u1_pre_topc(X16)))|v2_pre_topc(X16)|~l1_pre_topc(X16)))&(~r2_hidden(k9_subset_1(u1_struct_0(X16),esk3_1(X16),esk4_1(X16)),u1_pre_topc(X16))|(r1_tarski(esk2_1(X16),u1_pre_topc(X16))|~r2_hidden(u1_struct_0(X16),u1_pre_topc(X16)))|v2_pre_topc(X16)|~l1_pre_topc(X16)))))&((m1_subset_1(esk3_1(X16),k1_zfmisc_1(u1_struct_0(X16)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X16),esk2_1(X16)),u1_pre_topc(X16))|~r2_hidden(u1_struct_0(X16),u1_pre_topc(X16)))|v2_pre_topc(X16)|~l1_pre_topc(X16))&((m1_subset_1(esk4_1(X16),k1_zfmisc_1(u1_struct_0(X16)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X16),esk2_1(X16)),u1_pre_topc(X16))|~r2_hidden(u1_struct_0(X16),u1_pre_topc(X16)))|v2_pre_topc(X16)|~l1_pre_topc(X16))&(((r2_hidden(esk3_1(X16),u1_pre_topc(X16))|(~r2_hidden(k5_setfam_1(u1_struct_0(X16),esk2_1(X16)),u1_pre_topc(X16))|~r2_hidden(u1_struct_0(X16),u1_pre_topc(X16)))|v2_pre_topc(X16)|~l1_pre_topc(X16))&(r2_hidden(esk4_1(X16),u1_pre_topc(X16))|(~r2_hidden(k5_setfam_1(u1_struct_0(X16),esk2_1(X16)),u1_pre_topc(X16))|~r2_hidden(u1_struct_0(X16),u1_pre_topc(X16)))|v2_pre_topc(X16)|~l1_pre_topc(X16)))&(~r2_hidden(k9_subset_1(u1_struct_0(X16),esk3_1(X16),esk4_1(X16)),u1_pre_topc(X16))|(~r2_hidden(k5_setfam_1(u1_struct_0(X16),esk2_1(X16)),u1_pre_topc(X16))|~r2_hidden(u1_struct_0(X16),u1_pre_topc(X16)))|v2_pre_topc(X16)|~l1_pre_topc(X16)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.18/0.39  fof(c_0_26, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 0.18/0.39  cnf(c_0_27, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.39  cnf(c_0_28, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.39  cnf(c_0_29, plain, (k3_tarski(u1_pre_topc(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.18/0.39  cnf(c_0_30, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.39  fof(c_0_31, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk5_0)))!=u1_struct_0(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_26])])])])).
% 0.18/0.39  cnf(c_0_32, plain, (k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(csr,[status(thm)],[c_0_27, c_0_28])).
% 0.18/0.39  cnf(c_0_33, plain, (k3_tarski(u1_pre_topc(X1))=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.18/0.39  cnf(c_0_34, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk5_0)))!=u1_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.39  cnf(c_0_35, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_30])).
% 0.18/0.39  cnf(c_0_36, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.39  cnf(c_0_37, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.39  cnf(c_0_38, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37])]), ['proof']).
% 0.18/0.39  # SZS output end CNFRefutation
% 0.18/0.39  # Proof object total steps             : 39
% 0.18/0.39  # Proof object clause steps            : 20
% 0.18/0.39  # Proof object formula steps           : 19
% 0.18/0.39  # Proof object conjectures             : 7
% 0.18/0.39  # Proof object clause conjectures      : 4
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 11
% 0.18/0.39  # Proof object initial formulas used   : 9
% 0.18/0.39  # Proof object generating inferences   : 8
% 0.18/0.39  # Proof object simplifying inferences  : 5
% 0.18/0.39  # Training examples: 0 positive, 0 negative
% 0.18/0.39  # Parsed axioms                        : 9
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 32
% 0.18/0.39  # Removed in clause preprocessing      : 0
% 0.18/0.39  # Initial clauses in saturation        : 32
% 0.18/0.39  # Processed clauses                    : 63
% 0.18/0.39  # ...of these trivial                  : 0
% 0.18/0.39  # ...subsumed                          : 0
% 0.18/0.39  # ...remaining for further processing  : 63
% 0.18/0.39  # Other redundant clauses eliminated   : 0
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 0
% 0.18/0.39  # Backward-rewritten                   : 0
% 0.18/0.39  # Generated clauses                    : 18
% 0.18/0.39  # ...of the previous two non-trivial   : 12
% 0.18/0.39  # Contextual simplify-reflections      : 2
% 0.18/0.39  # Paramodulations                      : 18
% 0.18/0.39  # Factorizations                       : 0
% 0.18/0.39  # Equation resolutions                 : 0
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.39  #    Success case prop solver time     : 0.000
% 0.18/0.39  # Current number of processed clauses  : 31
% 0.18/0.39  #    Positive orientable unit clauses  : 2
% 0.18/0.39  #    Positive unorientable unit clauses: 0
% 0.18/0.39  #    Negative unit clauses             : 2
% 0.18/0.39  #    Non-unit-clauses                  : 27
% 0.18/0.39  # Current number of unprocessed clauses: 13
% 0.18/0.39  # ...number of literals in the above   : 65
% 0.18/0.39  # Current number of archived formulas  : 0
% 0.18/0.39  # Current number of archived clauses   : 32
% 0.18/0.39  # Clause-clause subsumption calls (NU) : 524
% 0.18/0.39  # Rec. Clause-clause subsumption calls : 37
% 0.18/0.39  # Non-unit clause-clause subsumptions  : 2
% 0.18/0.39  # Unit Clause-clause subsumption calls : 0
% 0.18/0.39  # Rewrite failures with RHS unbound    : 0
% 0.18/0.39  # BW rewrite match attempts            : 0
% 0.18/0.39  # BW rewrite match successes           : 0
% 0.18/0.39  # Condensation attempts                : 0
% 0.18/0.39  # Condensation successes               : 0
% 0.18/0.39  # Termbank termtop insertions          : 3395
% 0.18/0.40  
% 0.18/0.40  # -------------------------------------------------
% 0.18/0.40  # User time                : 0.055 s
% 0.18/0.40  # System time              : 0.003 s
% 0.18/0.40  # Total time               : 0.058 s
% 0.18/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
