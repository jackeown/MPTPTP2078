%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:14 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 121 expanded)
%              Number of clauses        :   34 (  53 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  123 ( 289 expanded)
%              Number of equality atoms :    6 (  24 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t31_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
             => m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

fof(t61_setfam_1,axiom,(
    ! [X1] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_11,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X20,X21,X22] :
      ( ~ r2_hidden(X20,X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(X22))
      | m1_subset_1(X20,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
               => m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_tops_2])).

fof(c_0_21,plain,(
    ! [X23] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X23))) ),
    inference(variable_rename,[status(thm)],[t61_setfam_1])).

fof(c_0_22,plain,(
    ! [X10] : k2_tarski(X10,X10) = k1_tarski(X10) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_23,plain,(
    ! [X11,X12] : k1_enumset1(X11,X11,X12) = k2_tarski(X11,X12) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X13] : ~ v1_xboole_0(k1_tarski(X13)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

fof(c_0_25,plain,(
    ! [X24,X25,X26] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_pre_topc(X25,X24)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    & ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_28,plain,(
    ! [X14,X15] :
      ( ~ v1_xboole_0(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | v1_xboole_0(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_29,plain,
    ( m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_14])).

fof(c_0_35,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X16,X17)
      | v1_xboole_0(X17)
      | r2_hidden(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( m1_subset_1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_39,plain,
    ( ~ v1_xboole_0(k1_enumset1(X1,X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_30]),c_0_31])).

cnf(c_0_40,plain,
    ( m1_subset_1(esk1_2(k1_zfmisc_1(u1_struct_0(X1)),X2),k1_zfmisc_1(u1_struct_0(X3)))
    | r1_tarski(k1_zfmisc_1(u1_struct_0(X1)),X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_36])).

cnf(c_0_45,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk1_2(k1_zfmisc_1(u1_struct_0(esk3_0)),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | r1_tarski(k1_zfmisc_1(u1_struct_0(esk3_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_47,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_2(k1_zfmisc_1(u1_struct_0(esk3_0)),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | r1_tarski(k1_zfmisc_1(u1_struct_0(esk3_0)),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_46]),c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk4_0)
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(esk3_0)),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(u1_struct_0(esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk1_2(X1,k1_zfmisc_1(u1_struct_0(esk2_0))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_14])).

cnf(c_0_55,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_54]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.38  fof(t31_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))=>m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 0.19/0.38  fof(t61_setfam_1, axiom, ![X1]:m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 0.19/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.38  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.19/0.38  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.19/0.38  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.19/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.38  fof(c_0_11, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.38  fof(c_0_12, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  cnf(c_0_13, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_14, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  fof(c_0_15, plain, ![X20, X21, X22]:(~r2_hidden(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(X22))|m1_subset_1(X20,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.38  cnf(c_0_16, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_17, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.38  cnf(c_0_18, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_19, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.38  fof(c_0_20, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))=>m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))))))), inference(assume_negation,[status(cth)],[t31_tops_2])).
% 0.19/0.38  fof(c_0_21, plain, ![X23]:m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X23))), inference(variable_rename,[status(thm)],[t61_setfam_1])).
% 0.19/0.38  fof(c_0_22, plain, ![X10]:k2_tarski(X10,X10)=k1_tarski(X10), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.38  fof(c_0_23, plain, ![X11, X12]:k1_enumset1(X11,X11,X12)=k2_tarski(X11,X12), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.38  fof(c_0_24, plain, ![X13]:~v1_xboole_0(k1_tarski(X13)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.19/0.38  fof(c_0_25, plain, ![X24, X25, X26]:(~l1_pre_topc(X24)|(~m1_pre_topc(X25,X24)|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.19/0.38  cnf(c_0_26, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.38  fof(c_0_27, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_pre_topc(esk3_0,esk2_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))&~m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.19/0.38  fof(c_0_28, plain, ![X14, X15]:(~v1_xboole_0(X14)|(~m1_subset_1(X15,k1_zfmisc_1(X14))|v1_xboole_0(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.19/0.38  cnf(c_0_29, plain, (m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_32, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_33, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_34, plain, (m1_subset_1(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_14])).
% 0.19/0.38  fof(c_0_35, plain, ![X16, X17]:(~m1_subset_1(X16,X17)|(v1_xboole_0(X17)|r2_hidden(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  cnf(c_0_37, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_38, plain, (m1_subset_1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.19/0.38  cnf(c_0_39, plain, (~v1_xboole_0(k1_enumset1(X1,X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_30]), c_0_31])).
% 0.19/0.38  cnf(c_0_40, plain, (m1_subset_1(esk1_2(k1_zfmisc_1(u1_struct_0(X1)),X2),k1_zfmisc_1(u1_struct_0(X3)))|r1_tarski(k1_zfmisc_1(u1_struct_0(X1)),X2)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  cnf(c_0_43, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_36])).
% 0.19/0.38  cnf(c_0_45, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk1_2(k1_zfmisc_1(u1_struct_0(esk3_0)),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|r1_tarski(k1_zfmisc_1(u1_struct_0(esk3_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.19/0.38  cnf(c_0_47, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_2(k1_zfmisc_1(u1_struct_0(esk3_0)),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|r1_tarski(k1_zfmisc_1(u1_struct_0(esk3_0)),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_46]), c_0_45])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,esk4_0)|~r1_tarski(k1_zfmisc_1(u1_struct_0(esk3_0)),X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (r1_tarski(k1_zfmisc_1(u1_struct_0(esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_13, c_0_49])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk1_2(X1,k1_zfmisc_1(u1_struct_0(esk2_0))),esk4_0)), inference(spm,[status(thm)],[c_0_13, c_0_52])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (r1_tarski(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_53, c_0_14])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_54]), c_0_55]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 57
% 0.19/0.38  # Proof object clause steps            : 34
% 0.19/0.38  # Proof object formula steps           : 23
% 0.19/0.38  # Proof object conjectures             : 17
% 0.19/0.38  # Proof object clause conjectures      : 14
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 16
% 0.19/0.38  # Proof object initial formulas used   : 11
% 0.19/0.38  # Proof object generating inferences   : 16
% 0.19/0.38  # Proof object simplifying inferences  : 10
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 11
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 17
% 0.19/0.38  # Removed in clause preprocessing      : 2
% 0.19/0.38  # Initial clauses in saturation        : 15
% 0.19/0.38  # Processed clauses                    : 207
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 53
% 0.19/0.38  # ...remaining for further processing  : 154
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 2
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 268
% 0.19/0.38  # ...of the previous two non-trivial   : 245
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 268
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 137
% 0.19/0.38  #    Positive orientable unit clauses  : 16
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 3
% 0.19/0.38  #    Non-unit-clauses                  : 118
% 0.19/0.38  # Current number of unprocessed clauses: 68
% 0.19/0.38  # ...number of literals in the above   : 248
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 19
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 904
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 603
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 53
% 0.19/0.38  # Unit Clause-clause subsumption calls : 22
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 21
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 5829
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.039 s
% 0.19/0.39  # System time              : 0.004 s
% 0.19/0.39  # Total time               : 0.043 s
% 0.19/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
