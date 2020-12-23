%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:59 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   42 (  72 expanded)
%              Number of clauses        :   21 (  28 expanded)
%              Number of leaves         :   10 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  196 ( 390 expanded)
%              Number of equality atoms :   19 (  40 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t24_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(fc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ~ v1_xboole_0(u1_pre_topc(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_pre_topc)).

fof(c_0_10,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_11,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | r1_tarski(X6,k3_tarski(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_12,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | r1_tarski(k3_tarski(X8),k3_tarski(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

fof(c_0_13,plain,(
    ! [X10] : k3_tarski(k1_zfmisc_1(X10)) = X10 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_14,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_19,plain,(
    ! [X26] :
      ( ~ l1_pre_topc(X26)
      | m1_subset_1(u1_pre_topc(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

cnf(c_0_21,plain,
    ( k3_tarski(X1) = X2
    | ~ r2_hidden(X2,X1)
    | ~ r1_tarski(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X17,X18,X19,X20] :
      ( ( r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))
        | ~ r1_tarski(X18,u1_pre_topc(X17))
        | r2_hidden(k5_setfam_1(u1_struct_0(X17),X18),u1_pre_topc(X17))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ r2_hidden(X19,u1_pre_topc(X17))
        | ~ r2_hidden(X20,u1_pre_topc(X17))
        | r2_hidden(k9_subset_1(u1_struct_0(X17),X19,X20),u1_pre_topc(X17))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk2_1(X17),k1_zfmisc_1(u1_struct_0(X17)))
        | m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk3_1(X17),k1_zfmisc_1(u1_struct_0(X17)))
        | m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r2_hidden(esk2_1(X17),u1_pre_topc(X17))
        | m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r2_hidden(esk3_1(X17),u1_pre_topc(X17))
        | m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X17),esk2_1(X17),esk3_1(X17)),u1_pre_topc(X17))
        | m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk2_1(X17),k1_zfmisc_1(u1_struct_0(X17)))
        | r1_tarski(esk1_1(X17),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk3_1(X17),k1_zfmisc_1(u1_struct_0(X17)))
        | r1_tarski(esk1_1(X17),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r2_hidden(esk2_1(X17),u1_pre_topc(X17))
        | r1_tarski(esk1_1(X17),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r2_hidden(esk3_1(X17),u1_pre_topc(X17))
        | r1_tarski(esk1_1(X17),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X17),esk2_1(X17),esk3_1(X17)),u1_pre_topc(X17))
        | r1_tarski(esk1_1(X17),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk2_1(X17),k1_zfmisc_1(u1_struct_0(X17)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk3_1(X17),k1_zfmisc_1(u1_struct_0(X17)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r2_hidden(esk2_1(X17),u1_pre_topc(X17))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( r2_hidden(esk3_1(X17),u1_pre_topc(X17))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X17),esk2_1(X17),esk3_1(X17)),u1_pre_topc(X17))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))
        | ~ r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))
        | v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

fof(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk4_0))) != u1_struct_0(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

cnf(c_0_27,plain,
    ( k3_tarski(X1) = X2
    | ~ r2_hidden(X2,X1)
    | ~ r1_tarski(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(u1_pre_topc(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X31] :
      ( v1_xboole_0(X31)
      | ~ r2_hidden(k3_tarski(X31),X31)
      | k4_yellow_0(k2_yellow_1(X31)) = k3_tarski(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

cnf(c_0_33,plain,
    ( k3_tarski(u1_pre_topc(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

fof(c_0_35,plain,(
    ! [X27] :
      ( ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | ~ v1_xboole_0(u1_pre_topc(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_pre_topc])])])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk4_0)) = u1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_31])])).

cnf(c_0_38,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk4_0))) != u1_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_pre_topc(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(u1_pre_topc(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_34])]),c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_30]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:53:55 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.13/0.38  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.13/0.38  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.13/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.38  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.13/0.38  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_yellow_1)).
% 0.13/0.38  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.13/0.38  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.13/0.38  fof(fc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>~(v1_xboole_0(u1_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_pre_topc)).
% 0.13/0.38  fof(c_0_10, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X6, X7]:(~r2_hidden(X6,X7)|r1_tarski(X6,k3_tarski(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.13/0.38  fof(c_0_12, plain, ![X8, X9]:(~r1_tarski(X8,X9)|r1_tarski(k3_tarski(X8),k3_tarski(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.13/0.38  fof(c_0_13, plain, ![X10]:k3_tarski(k1_zfmisc_1(X10))=X10, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.13/0.38  cnf(c_0_14, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_15, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_16, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_17, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_18, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.38  fof(c_0_19, plain, ![X26]:(~l1_pre_topc(X26)|m1_subset_1(u1_pre_topc(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.13/0.38  fof(c_0_20, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 0.13/0.38  cnf(c_0_21, plain, (k3_tarski(X1)=X2|~r2_hidden(X2,X1)|~r1_tarski(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.38  cnf(c_0_22, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.38  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_24, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  fof(c_0_25, plain, ![X17, X18, X19, X20]:((((r2_hidden(u1_struct_0(X17),u1_pre_topc(X17))|~v2_pre_topc(X17)|~l1_pre_topc(X17))&(~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))|(~r1_tarski(X18,u1_pre_topc(X17))|r2_hidden(k5_setfam_1(u1_struct_0(X17),X18),u1_pre_topc(X17)))|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X17)))|(~r2_hidden(X19,u1_pre_topc(X17))|~r2_hidden(X20,u1_pre_topc(X17))|r2_hidden(k9_subset_1(u1_struct_0(X17),X19,X20),u1_pre_topc(X17))))|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(((m1_subset_1(esk2_1(X17),k1_zfmisc_1(u1_struct_0(X17)))|(m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17))&((m1_subset_1(esk3_1(X17),k1_zfmisc_1(u1_struct_0(X17)))|(m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17))&(((r2_hidden(esk2_1(X17),u1_pre_topc(X17))|(m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17))&(r2_hidden(esk3_1(X17),u1_pre_topc(X17))|(m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17)))&(~r2_hidden(k9_subset_1(u1_struct_0(X17),esk2_1(X17),esk3_1(X17)),u1_pre_topc(X17))|(m1_subset_1(esk1_1(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17)))))&(((m1_subset_1(esk2_1(X17),k1_zfmisc_1(u1_struct_0(X17)))|(r1_tarski(esk1_1(X17),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17))&((m1_subset_1(esk3_1(X17),k1_zfmisc_1(u1_struct_0(X17)))|(r1_tarski(esk1_1(X17),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17))&(((r2_hidden(esk2_1(X17),u1_pre_topc(X17))|(r1_tarski(esk1_1(X17),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17))&(r2_hidden(esk3_1(X17),u1_pre_topc(X17))|(r1_tarski(esk1_1(X17),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17)))&(~r2_hidden(k9_subset_1(u1_struct_0(X17),esk2_1(X17),esk3_1(X17)),u1_pre_topc(X17))|(r1_tarski(esk1_1(X17),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17)))))&((m1_subset_1(esk2_1(X17),k1_zfmisc_1(u1_struct_0(X17)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17))&((m1_subset_1(esk3_1(X17),k1_zfmisc_1(u1_struct_0(X17)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17))&(((r2_hidden(esk2_1(X17),u1_pre_topc(X17))|(~r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17))&(r2_hidden(esk3_1(X17),u1_pre_topc(X17))|(~r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17)))&(~r2_hidden(k9_subset_1(u1_struct_0(X17),esk2_1(X17),esk3_1(X17)),u1_pre_topc(X17))|(~r2_hidden(k5_setfam_1(u1_struct_0(X17),esk1_1(X17)),u1_pre_topc(X17))|~r2_hidden(u1_struct_0(X17),u1_pre_topc(X17)))|v2_pre_topc(X17)|~l1_pre_topc(X17)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.13/0.38  fof(c_0_26, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk4_0)))!=u1_struct_0(esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.13/0.38  cnf(c_0_27, plain, (k3_tarski(X1)=X2|~r2_hidden(X2,X1)|~r1_tarski(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.38  cnf(c_0_28, plain, (r1_tarski(u1_pre_topc(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.38  cnf(c_0_29, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  fof(c_0_32, plain, ![X31]:(v1_xboole_0(X31)|(~r2_hidden(k3_tarski(X31),X31)|k4_yellow_0(k2_yellow_1(X31))=k3_tarski(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.13/0.38  cnf(c_0_33, plain, (k3_tarski(u1_pre_topc(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.13/0.38  fof(c_0_35, plain, ![X27]:(~v2_pre_topc(X27)|~l1_pre_topc(X27)|~v1_xboole_0(u1_pre_topc(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_pre_topc])])])).
% 0.13/0.38  cnf(c_0_36, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (k3_tarski(u1_pre_topc(esk4_0))=u1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_31])])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk4_0)))!=u1_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_39, plain, (~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_pre_topc(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (v1_xboole_0(u1_pre_topc(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_34])]), c_0_38])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_30]), c_0_31])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 42
% 0.13/0.38  # Proof object clause steps            : 21
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 10
% 0.13/0.38  # Proof object clause conjectures      : 7
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 12
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 9
% 0.13/0.38  # Proof object simplifying inferences  : 10
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 15
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 39
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 39
% 0.13/0.38  # Processed clauses                    : 96
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 4
% 0.13/0.38  # ...remaining for further processing  : 92
% 0.13/0.38  # Other redundant clauses eliminated   : 2
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 71
% 0.13/0.38  # ...of the previous two non-trivial   : 55
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 69
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 2
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 52
% 0.13/0.38  #    Positive orientable unit clauses  : 8
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 42
% 0.13/0.38  # Current number of unprocessed clauses: 36
% 0.13/0.38  # ...number of literals in the above   : 117
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 38
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 561
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 48
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.38  # Unit Clause-clause subsumption calls : 14
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4913
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.032 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.038 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
