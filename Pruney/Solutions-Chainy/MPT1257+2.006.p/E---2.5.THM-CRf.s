%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:11 EST 2020

% Result     : Theorem 5.32s
% Output     : CNFRefutation 5.32s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 168 expanded)
%              Number of clauses        :   26 (  64 expanded)
%              Number of leaves         :   10 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :  114 ( 406 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_xboole_0(k1_tops_1(X1,X2),k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(commutativity_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k4_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(t41_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(t43_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,X3)
          <=> r1_tarski(X2,k3_subset_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => r1_xboole_0(k1_tops_1(X1,X2),k2_tops_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t73_tops_1])).

fof(c_0_11,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | m1_subset_1(k2_tops_1(X20,X21),k1_zfmisc_1(u1_struct_0(X20))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

fof(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r1_xboole_0(k1_tops_1(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | m1_subset_1(k3_subset_1(X7,X8),k1_zfmisc_1(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_14,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | k2_tops_1(X22,X23) = k2_tops_1(X22,k3_subset_1(u1_struct_0(X22),X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

fof(c_0_15,plain,(
    ! [X4,X5,X6] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(X4))
      | k4_subset_1(X4,X5,X6) = k4_subset_1(X4,X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k4_subset_1])])).

cnf(c_0_16,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | k2_pre_topc(X24,X25) = k4_subset_1(u1_struct_0(X24),X25,k2_tops_1(X24,X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | ~ m1_subset_1(X11,k1_zfmisc_1(X9))
      | m1_subset_1(k4_subset_1(X9,X10,X11),k1_zfmisc_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

fof(c_0_23,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | ~ m1_subset_1(X14,k1_zfmisc_1(X12))
      | r1_tarski(k3_subset_1(X12,k4_subset_1(X12,X13,X14)),k3_subset_1(X12,X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_subset_1])])])).

cnf(c_0_24,plain,
    ( k4_subset_1(X2,X1,X3) = k4_subset_1(X2,X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_26,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( k2_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_18])])).

cnf(c_0_29,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | k1_tops_1(X18,X19) = k3_subset_1(u1_struct_0(X18),k2_pre_topc(X18,k3_subset_1(u1_struct_0(X18),X19))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

cnf(c_0_31,plain,
    ( r1_tarski(k3_subset_1(X2,k4_subset_1(X2,X1,X3)),k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,k2_tops_1(esk1_0,esk2_0)) = k4_subset_1(u1_struct_0(esk1_0),k2_tops_1(esk1_0,esk2_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_18])]),c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k4_subset_1(u1_struct_0(esk1_0),X1,k2_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_25])).

cnf(c_0_35,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X15,X16,X17] :
      ( ( ~ r1_xboole_0(X16,X17)
        | r1_tarski(X16,k3_subset_1(X15,X17))
        | ~ m1_subset_1(X17,k1_zfmisc_1(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(X15)) )
      & ( ~ r1_tarski(X16,k3_subset_1(X15,X17))
        | r1_xboole_0(X16,X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k4_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))),k3_subset_1(u1_struct_0(esk1_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k2_tops_1(esk1_0,esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_27]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_xboole_0(k1_tops_1(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_17]),c_0_18])])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))),k3_subset_1(u1_struct_0(esk1_0),k2_tops_1(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_25]),c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))),k2_tops_1(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_25]),c_0_44])]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:58:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 5.32/5.54  # AutoSched0-Mode selected heuristic G_E___200_B02_F1_AE_CS_SP_PI_S0S
% 5.32/5.54  # and selection function SelectComplexG.
% 5.32/5.54  #
% 5.32/5.54  # Preprocessing time       : 0.028 s
% 5.32/5.54  
% 5.32/5.54  # Proof found!
% 5.32/5.54  # SZS status Theorem
% 5.32/5.54  # SZS output start CNFRefutation
% 5.32/5.54  fof(t73_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_xboole_0(k1_tops_1(X1,X2),k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_tops_1)).
% 5.32/5.54  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.32/5.54  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.32/5.54  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 5.32/5.54  fof(commutativity_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k4_subset_1(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 5.32/5.54  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.32/5.54  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 5.32/5.54  fof(t41_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 5.32/5.54  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 5.32/5.54  fof(t43_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,X3)<=>r1_tarski(X2,k3_subset_1(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 5.32/5.54  fof(c_0_10, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_xboole_0(k1_tops_1(X1,X2),k2_tops_1(X1,X2))))), inference(assume_negation,[status(cth)],[t73_tops_1])).
% 5.32/5.54  fof(c_0_11, plain, ![X20, X21]:(~l1_pre_topc(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|m1_subset_1(k2_tops_1(X20,X21),k1_zfmisc_1(u1_struct_0(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 5.32/5.54  fof(c_0_12, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&~r1_xboole_0(k1_tops_1(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 5.32/5.54  fof(c_0_13, plain, ![X7, X8]:(~m1_subset_1(X8,k1_zfmisc_1(X7))|m1_subset_1(k3_subset_1(X7,X8),k1_zfmisc_1(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 5.32/5.54  fof(c_0_14, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|k2_tops_1(X22,X23)=k2_tops_1(X22,k3_subset_1(u1_struct_0(X22),X23)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 5.32/5.54  fof(c_0_15, plain, ![X4, X5, X6]:(~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X6,k1_zfmisc_1(X4))|k4_subset_1(X4,X5,X6)=k4_subset_1(X4,X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k4_subset_1])])).
% 5.32/5.54  cnf(c_0_16, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 5.32/5.54  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 5.32/5.54  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 5.32/5.54  fof(c_0_19, plain, ![X24, X25]:(~l1_pre_topc(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|k2_pre_topc(X24,X25)=k4_subset_1(u1_struct_0(X24),X25,k2_tops_1(X24,X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 5.32/5.54  cnf(c_0_20, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 5.32/5.54  cnf(c_0_21, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 5.32/5.54  fof(c_0_22, plain, ![X9, X10, X11]:(~m1_subset_1(X10,k1_zfmisc_1(X9))|~m1_subset_1(X11,k1_zfmisc_1(X9))|m1_subset_1(k4_subset_1(X9,X10,X11),k1_zfmisc_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 5.32/5.54  fof(c_0_23, plain, ![X12, X13, X14]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|(~m1_subset_1(X14,k1_zfmisc_1(X12))|r1_tarski(k3_subset_1(X12,k4_subset_1(X12,X13,X14)),k3_subset_1(X12,X13)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_subset_1])])])).
% 5.32/5.54  cnf(c_0_24, plain, (k4_subset_1(X2,X1,X3)=k4_subset_1(X2,X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.32/5.54  cnf(c_0_25, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 5.32/5.54  cnf(c_0_26, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 5.32/5.54  cnf(c_0_27, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_20, c_0_17])).
% 5.32/5.54  cnf(c_0_28, negated_conjecture, (k2_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_18])])).
% 5.32/5.54  cnf(c_0_29, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.32/5.54  fof(c_0_30, plain, ![X18, X19]:(~l1_pre_topc(X18)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|k1_tops_1(X18,X19)=k3_subset_1(u1_struct_0(X18),k2_pre_topc(X18,k3_subset_1(u1_struct_0(X18),X19))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 5.32/5.54  cnf(c_0_31, plain, (r1_tarski(k3_subset_1(X2,k4_subset_1(X2,X1,X3)),k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.32/5.54  cnf(c_0_32, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,k2_tops_1(esk1_0,esk2_0))=k4_subset_1(u1_struct_0(esk1_0),k2_tops_1(esk1_0,esk2_0),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 5.32/5.54  cnf(c_0_33, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_18])]), c_0_28])).
% 5.32/5.54  cnf(c_0_34, negated_conjecture, (m1_subset_1(k4_subset_1(u1_struct_0(esk1_0),X1,k2_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_29, c_0_25])).
% 5.32/5.54  cnf(c_0_35, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 5.32/5.54  fof(c_0_36, plain, ![X15, X16, X17]:((~r1_xboole_0(X16,X17)|r1_tarski(X16,k3_subset_1(X15,X17))|~m1_subset_1(X17,k1_zfmisc_1(X15))|~m1_subset_1(X16,k1_zfmisc_1(X15)))&(~r1_tarski(X16,k3_subset_1(X15,X17))|r1_xboole_0(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X15))|~m1_subset_1(X16,k1_zfmisc_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).
% 5.32/5.54  cnf(c_0_37, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k4_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))),k3_subset_1(u1_struct_0(esk1_0),X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_31, c_0_27])).
% 5.32/5.54  cnf(c_0_38, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k2_tops_1(esk1_0,esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_27]), c_0_33])).
% 5.32/5.54  cnf(c_0_39, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_27]), c_0_33])).
% 5.32/5.54  cnf(c_0_40, negated_conjecture, (~r1_xboole_0(k1_tops_1(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 5.32/5.54  cnf(c_0_41, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_17]), c_0_18])])).
% 5.32/5.54  cnf(c_0_42, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,k3_subset_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 5.32/5.54  cnf(c_0_43, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))),k3_subset_1(u1_struct_0(esk1_0),k2_tops_1(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_25]), c_0_38])).
% 5.32/5.54  cnf(c_0_44, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_20, c_0_39])).
% 5.32/5.54  cnf(c_0_45, negated_conjecture, (~r1_xboole_0(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))),k2_tops_1(esk1_0,esk2_0))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 5.32/5.54  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_25]), c_0_44])]), c_0_45]), ['proof']).
% 5.32/5.54  # SZS output end CNFRefutation
% 5.32/5.54  # Proof object total steps             : 47
% 5.32/5.54  # Proof object clause steps            : 26
% 5.32/5.54  # Proof object formula steps           : 21
% 5.32/5.54  # Proof object conjectures             : 20
% 5.32/5.54  # Proof object clause conjectures      : 17
% 5.32/5.54  # Proof object formula conjectures     : 3
% 5.32/5.54  # Proof object initial clauses used    : 12
% 5.32/5.54  # Proof object initial formulas used   : 10
% 5.32/5.54  # Proof object generating inferences   : 13
% 5.32/5.54  # Proof object simplifying inferences  : 17
% 5.32/5.54  # Training examples: 0 positive, 0 negative
% 5.32/5.54  # Parsed axioms                        : 10
% 5.32/5.54  # Removed by relevancy pruning/SinE    : 0
% 5.32/5.54  # Initial clauses                      : 13
% 5.32/5.54  # Removed in clause preprocessing      : 0
% 5.32/5.54  # Initial clauses in saturation        : 13
% 5.32/5.54  # Processed clauses                    : 2547
% 5.32/5.54  # ...of these trivial                  : 44
% 5.32/5.54  # ...subsumed                          : 60
% 5.32/5.54  # ...remaining for further processing  : 2443
% 5.32/5.54  # Other redundant clauses eliminated   : 0
% 5.32/5.54  # Clauses deleted for lack of memory   : 0
% 5.32/5.54  # Backward-subsumed                    : 0
% 5.32/5.54  # Backward-rewritten                   : 223
% 5.32/5.54  # Generated clauses                    : 855183
% 5.32/5.54  # ...of the previous two non-trivial   : 855238
% 5.32/5.54  # Contextual simplify-reflections      : 0
% 5.32/5.54  # Paramodulations                      : 855183
% 5.32/5.54  # Factorizations                       : 0
% 5.32/5.54  # Equation resolutions                 : 0
% 5.32/5.54  # Propositional unsat checks           : 0
% 5.32/5.54  #    Propositional check models        : 0
% 5.32/5.54  #    Propositional check unsatisfiable : 0
% 5.32/5.54  #    Propositional clauses             : 0
% 5.32/5.54  #    Propositional clauses after purity: 0
% 5.32/5.54  #    Propositional unsat core size     : 0
% 5.32/5.54  #    Propositional preprocessing time  : 0.000
% 5.32/5.54  #    Propositional encoding time       : 0.000
% 5.32/5.54  #    Propositional solver time         : 0.000
% 5.32/5.54  #    Success case prop preproc time    : 0.000
% 5.32/5.54  #    Success case prop encoding time   : 0.000
% 5.32/5.54  #    Success case prop solver time     : 0.000
% 5.32/5.54  # Current number of processed clauses  : 2220
% 5.32/5.54  #    Positive orientable unit clauses  : 1328
% 5.32/5.54  #    Positive unorientable unit clauses: 0
% 5.32/5.54  #    Negative unit clauses             : 1
% 5.32/5.54  #    Non-unit-clauses                  : 891
% 5.32/5.54  # Current number of unprocessed clauses: 852370
% 5.32/5.54  # ...number of literals in the above   : 858685
% 5.32/5.54  # Current number of archived formulas  : 0
% 5.32/5.54  # Current number of archived clauses   : 223
% 5.32/5.54  # Clause-clause subsumption calls (NU) : 41856
% 5.32/5.54  # Rec. Clause-clause subsumption calls : 41855
% 5.32/5.54  # Non-unit clause-clause subsumptions  : 60
% 5.32/5.54  # Unit Clause-clause subsumption calls : 16145
% 5.32/5.54  # Rewrite failures with RHS unbound    : 0
% 5.32/5.54  # BW rewrite match attempts            : 102201
% 5.32/5.54  # BW rewrite match successes           : 106
% 5.32/5.54  # Condensation attempts                : 0
% 5.32/5.54  # Condensation successes               : 0
% 5.32/5.54  # Termbank termtop insertions          : 35881183
% 5.39/5.58  
% 5.39/5.58  # -------------------------------------------------
% 5.39/5.58  # User time                : 4.825 s
% 5.39/5.58  # System time              : 0.407 s
% 5.39/5.58  # Total time               : 5.232 s
% 5.39/5.58  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
