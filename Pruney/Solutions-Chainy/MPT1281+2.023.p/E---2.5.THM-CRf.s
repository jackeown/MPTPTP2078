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
% DateTime   : Thu Dec  3 11:12:32 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 (  74 expanded)
%              Number of clauses        :   24 (  29 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  127 ( 214 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(commutativity_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k4_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t103_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v5_tops_1(X2,X1)
           => r1_tarski(k2_tops_1(X1,X2),k2_pre_topc(X1,k1_tops_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(t72_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X2)),k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).

fof(d7_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v5_tops_1(X2,X1)
          <=> X2 = k2_pre_topc(X1,k1_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(c_0_11,plain,(
    ! [X7,X8] : r1_tarski(X7,k2_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_12,plain,(
    ! [X9,X10] : k3_tarski(k2_tarski(X9,X10)) = k2_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
      | k4_subset_1(X14,X15,X16) = k2_xboole_0(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_tarski(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_15])).

fof(c_0_19,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | ~ m1_subset_1(X13,k1_zfmisc_1(X11))
      | k4_subset_1(X11,X12,X13) = k4_subset_1(X11,X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k4_subset_1])])).

fof(c_0_20,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X5,X6)
      | r1_tarski(X4,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,k4_subset_1(X2,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( k4_subset_1(X2,X1,X3) = k4_subset_1(X2,X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v5_tops_1(X2,X1)
             => r1_tarski(k2_tops_1(X1,X2),k2_pre_topc(X1,k1_tops_1(X1,X2))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t103_tops_1])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k4_subset_1(X2,X3,X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_26,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | k2_pre_topc(X23,X24) = k4_subset_1(u1_struct_0(X23),X24,k2_tops_1(X23,X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

fof(c_0_27,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | m1_subset_1(k2_tops_1(X21,X22),k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

fof(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v5_tops_1(esk2_0,esk1_0)
    & ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k4_subset_1(X2,X3,X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X25,X26] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | r1_tarski(k2_tops_1(X25,k2_pre_topc(X25,X26)),k2_tops_1(X25,X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_tops_1])])])).

fof(c_0_33,plain,(
    ! [X17,X18] :
      ( ( ~ v5_tops_1(X18,X17)
        | X18 = k2_pre_topc(X17,k1_tops_1(X17,X18))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( X18 != k2_pre_topc(X17,k1_tops_1(X17,X18))
        | v5_tops_1(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tops_1])])])])).

fof(c_0_34,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | m1_subset_1(k1_tops_1(X19,X20),k1_zfmisc_1(u1_struct_0(X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_tops_1(X2,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X2)),k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( X1 = k2_pre_topc(X2,k1_tops_1(X2,X1))
    | ~ v5_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),k2_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_42,plain,
    ( r1_tarski(k2_tops_1(X1,X2),k2_tops_1(X1,k1_tops_1(X1,X2)))
    | ~ v5_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( v5_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_37]),c_0_44])])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_40]),c_0_37]),c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:22:37 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.018 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.40  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.40  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.19/0.40  fof(commutativity_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k4_subset_1(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 0.19/0.40  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.40  fof(t103_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v5_tops_1(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),k2_pre_topc(X1,k1_tops_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tops_1)).
% 0.19/0.40  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 0.19/0.40  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 0.19/0.40  fof(t72_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X2)),k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tops_1)).
% 0.19/0.40  fof(d7_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v5_tops_1(X2,X1)<=>X2=k2_pre_topc(X1,k1_tops_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 0.19/0.40  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.19/0.40  fof(c_0_11, plain, ![X7, X8]:r1_tarski(X7,k2_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.40  fof(c_0_12, plain, ![X9, X10]:k3_tarski(k2_tarski(X9,X10))=k2_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.40  fof(c_0_13, plain, ![X14, X15, X16]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|~m1_subset_1(X16,k1_zfmisc_1(X14))|k4_subset_1(X14,X15,X16)=k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.19/0.40  cnf(c_0_14, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_15, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_16, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_17, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.40  cnf(c_0_18, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_tarski(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_16, c_0_15])).
% 0.19/0.40  fof(c_0_19, plain, ![X11, X12, X13]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|~m1_subset_1(X13,k1_zfmisc_1(X11))|k4_subset_1(X11,X12,X13)=k4_subset_1(X11,X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k4_subset_1])])).
% 0.19/0.40  fof(c_0_20, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|~r1_tarski(X5,X6)|r1_tarski(X4,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.40  cnf(c_0_21, plain, (r1_tarski(X1,k4_subset_1(X2,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.40  cnf(c_0_22, plain, (k4_subset_1(X2,X1,X3)=k4_subset_1(X2,X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  fof(c_0_23, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v5_tops_1(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),k2_pre_topc(X1,k1_tops_1(X1,X2))))))), inference(assume_negation,[status(cth)],[t103_tops_1])).
% 0.19/0.40  cnf(c_0_24, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_25, plain, (r1_tarski(X1,k4_subset_1(X2,X3,X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.40  fof(c_0_26, plain, ![X23, X24]:(~l1_pre_topc(X23)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|k2_pre_topc(X23,X24)=k4_subset_1(u1_struct_0(X23),X24,k2_tops_1(X23,X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 0.19/0.40  fof(c_0_27, plain, ![X21, X22]:(~l1_pre_topc(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|m1_subset_1(k2_tops_1(X21,X22),k1_zfmisc_1(u1_struct_0(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 0.19/0.40  fof(c_0_28, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(v5_tops_1(esk2_0,esk1_0)&~r1_tarski(k2_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.19/0.40  cnf(c_0_29, plain, (r1_tarski(X1,k4_subset_1(X2,X3,X4))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.40  cnf(c_0_30, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_31, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.40  fof(c_0_32, plain, ![X25, X26]:(~l1_pre_topc(X25)|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|r1_tarski(k2_tops_1(X25,k2_pre_topc(X25,X26)),k2_tops_1(X25,X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_tops_1])])])).
% 0.19/0.40  fof(c_0_33, plain, ![X17, X18]:((~v5_tops_1(X18,X17)|X18=k2_pre_topc(X17,k1_tops_1(X17,X18))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X17))&(X18!=k2_pre_topc(X17,k1_tops_1(X17,X18))|v5_tops_1(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tops_1])])])])).
% 0.19/0.40  fof(c_0_34, plain, ![X19, X20]:(~l1_pre_topc(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|m1_subset_1(k1_tops_1(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.19/0.40  cnf(c_0_35, negated_conjecture, (~r1_tarski(k2_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_36, plain, (r1_tarski(X1,k2_pre_topc(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_tops_1(X2,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.19/0.40  cnf(c_0_37, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_38, plain, (r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X2)),k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.40  cnf(c_0_39, plain, (X1=k2_pre_topc(X2,k1_tops_1(X2,X1))|~v5_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.40  cnf(c_0_40, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_41, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k2_tops_1(esk1_0,esk2_0),k2_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.19/0.40  cnf(c_0_42, plain, (r1_tarski(k2_tops_1(X1,X2),k2_tops_1(X1,k1_tops_1(X1,X2)))|~v5_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.19/0.40  cnf(c_0_43, negated_conjecture, (v5_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_37]), c_0_44])])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_40]), c_0_37]), c_0_44])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 47
% 0.19/0.40  # Proof object clause steps            : 24
% 0.19/0.40  # Proof object formula steps           : 23
% 0.19/0.40  # Proof object conjectures             : 10
% 0.19/0.40  # Proof object clause conjectures      : 7
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 14
% 0.19/0.40  # Proof object initial formulas used   : 11
% 0.19/0.40  # Proof object generating inferences   : 8
% 0.19/0.40  # Proof object simplifying inferences  : 13
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 11
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 15
% 0.19/0.40  # Removed in clause preprocessing      : 1
% 0.19/0.40  # Initial clauses in saturation        : 14
% 0.19/0.40  # Processed clauses                    : 354
% 0.19/0.40  # ...of these trivial                  : 0
% 0.19/0.40  # ...subsumed                          : 118
% 0.19/0.40  # ...remaining for further processing  : 236
% 0.19/0.40  # Other redundant clauses eliminated   : 0
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 13
% 0.19/0.40  # Backward-rewritten                   : 0
% 0.19/0.40  # Generated clauses                    : 1831
% 0.19/0.40  # ...of the previous two non-trivial   : 1818
% 0.19/0.40  # Contextual simplify-reflections      : 5
% 0.19/0.40  # Paramodulations                      : 1831
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 0
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
% 0.19/0.40  # Current number of processed clauses  : 209
% 0.19/0.40  #    Positive orientable unit clauses  : 6
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 3
% 0.19/0.40  #    Non-unit-clauses                  : 200
% 0.19/0.40  # Current number of unprocessed clauses: 1490
% 0.19/0.40  # ...number of literals in the above   : 6968
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 28
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 11656
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 4149
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 136
% 0.19/0.40  # Unit Clause-clause subsumption calls : 211
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 36
% 0.19/0.40  # BW rewrite match successes           : 0
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 46342
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.059 s
% 0.19/0.40  # System time              : 0.004 s
% 0.19/0.40  # Total time               : 0.063 s
% 0.19/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
