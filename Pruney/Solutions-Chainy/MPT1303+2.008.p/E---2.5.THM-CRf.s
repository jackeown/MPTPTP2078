%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:04 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   30 (  58 expanded)
%              Number of clauses        :   17 (  23 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 171 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t21_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( v1_tops_2(X2,X1)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tops_2)).

fof(t18_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( ( r1_tarski(X2,X3)
                  & v1_tops_2(X3,X1) )
               => v1_tops_2(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(c_0_6,plain,(
    ! [X46,X47,X48] :
      ( ~ m1_subset_1(X48,k1_zfmisc_1(X46))
      | k9_subset_1(X46,X47,X48) = k3_xboole_0(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_7,plain,(
    ! [X27,X28] : k4_xboole_0(X27,k4_xboole_0(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ( v1_tops_2(X2,X1)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t21_tops_2])).

cnf(c_0_9,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    & v1_tops_2(esk5_0,esk4_0)
    & ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(esk4_0)),esk5_0,esk6_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_12,plain,(
    ! [X56,X57,X58] :
      ( ~ l1_pre_topc(X56)
      | ~ m1_subset_1(X57,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X56))))
      | ~ m1_subset_1(X58,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X56))))
      | ~ r1_tarski(X57,X58)
      | ~ v1_tops_2(X58,X56)
      | v1_tops_2(X57,X56) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tops_2])])])).

fof(c_0_13,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X42))
      | m1_subset_1(k9_subset_1(X42,X43,X44),k1_zfmisc_1(X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_14,plain,
    ( k9_subset_1(X2,X3,X1) = k4_xboole_0(X3,k4_xboole_0(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_tops_2(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X3)
    | ~ v1_tops_2(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v1_tops_2(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(esk4_0)),X1,esk6_0) = k4_xboole_0(X1,k4_xboole_0(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(esk4_0)),esk5_0,esk6_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( v1_tops_2(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,esk6_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_15])])).

fof(c_0_25,plain,(
    ! [X25,X26] : r1_tarski(k4_xboole_0(X25,X26),X25) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_tops_2(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),esk4_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( v1_tops_2(k4_xboole_0(X1,k4_xboole_0(X1,esk6_0)),esk4_0)
    | ~ r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:10:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.19/0.45  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.028 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.19/0.45  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.45  fof(t21_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)=>v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_tops_2)).
% 0.19/0.45  fof(t18_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>((r1_tarski(X2,X3)&v1_tops_2(X3,X1))=>v1_tops_2(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tops_2)).
% 0.19/0.45  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.19/0.45  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.45  fof(c_0_6, plain, ![X46, X47, X48]:(~m1_subset_1(X48,k1_zfmisc_1(X46))|k9_subset_1(X46,X47,X48)=k3_xboole_0(X47,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.19/0.45  fof(c_0_7, plain, ![X27, X28]:k4_xboole_0(X27,k4_xboole_0(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.45  fof(c_0_8, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)=>v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t21_tops_2])).
% 0.19/0.45  cnf(c_0_9, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.45  cnf(c_0_10, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.45  fof(c_0_11, negated_conjecture, (l1_pre_topc(esk4_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))&(m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))&(v1_tops_2(esk5_0,esk4_0)&~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(esk4_0)),esk5_0,esk6_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.19/0.45  fof(c_0_12, plain, ![X56, X57, X58]:(~l1_pre_topc(X56)|(~m1_subset_1(X57,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X56))))|(~m1_subset_1(X58,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X56))))|(~r1_tarski(X57,X58)|~v1_tops_2(X58,X56)|v1_tops_2(X57,X56))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_tops_2])])])).
% 0.19/0.45  fof(c_0_13, plain, ![X42, X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(X42))|m1_subset_1(k9_subset_1(X42,X43,X44),k1_zfmisc_1(X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.19/0.45  cnf(c_0_14, plain, (k9_subset_1(X2,X3,X1)=k4_xboole_0(X3,k4_xboole_0(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.19/0.45  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.45  cnf(c_0_16, plain, (v1_tops_2(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~r1_tarski(X2,X3)|~v1_tops_2(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.45  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.45  cnf(c_0_18, negated_conjecture, (v1_tops_2(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.45  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.45  cnf(c_0_20, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.45  cnf(c_0_21, negated_conjecture, (k9_subset_1(k1_zfmisc_1(u1_struct_0(esk4_0)),X1,esk6_0)=k4_xboole_0(X1,k4_xboole_0(X1,esk6_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.45  cnf(c_0_22, negated_conjecture, (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(esk4_0)),esk5_0,esk6_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.45  cnf(c_0_23, negated_conjecture, (v1_tops_2(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))|~r1_tarski(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])])).
% 0.19/0.45  cnf(c_0_24, negated_conjecture, (m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,esk6_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_15])])).
% 0.19/0.45  fof(c_0_25, plain, ![X25, X26]:r1_tarski(k4_xboole_0(X25,X26),X25), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.45  cnf(c_0_26, negated_conjecture, (~v1_tops_2(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)),esk4_0)), inference(rw,[status(thm)],[c_0_22, c_0_21])).
% 0.19/0.45  cnf(c_0_27, negated_conjecture, (v1_tops_2(k4_xboole_0(X1,k4_xboole_0(X1,esk6_0)),esk4_0)|~r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.45  cnf(c_0_28, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.45  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 30
% 0.19/0.45  # Proof object clause steps            : 17
% 0.19/0.45  # Proof object formula steps           : 13
% 0.19/0.45  # Proof object conjectures             : 14
% 0.19/0.45  # Proof object clause conjectures      : 11
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 10
% 0.19/0.45  # Proof object initial formulas used   : 6
% 0.19/0.45  # Proof object generating inferences   : 5
% 0.19/0.45  # Proof object simplifying inferences  : 9
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 22
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 36
% 0.19/0.45  # Removed in clause preprocessing      : 1
% 0.19/0.45  # Initial clauses in saturation        : 35
% 0.19/0.45  # Processed clauses                    : 1170
% 0.19/0.45  # ...of these trivial                  : 15
% 0.19/0.45  # ...subsumed                          : 732
% 0.19/0.45  # ...remaining for further processing  : 423
% 0.19/0.45  # Other redundant clauses eliminated   : 6
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 12
% 0.19/0.45  # Backward-rewritten                   : 9
% 0.19/0.45  # Generated clauses                    : 4339
% 0.19/0.45  # ...of the previous two non-trivial   : 3411
% 0.19/0.45  # Contextual simplify-reflections      : 2
% 0.19/0.45  # Paramodulations                      : 4329
% 0.19/0.45  # Factorizations                       : 0
% 0.19/0.45  # Equation resolutions                 : 10
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 367
% 0.19/0.45  #    Positive orientable unit clauses  : 48
% 0.19/0.45  #    Positive unorientable unit clauses: 3
% 0.19/0.45  #    Negative unit clauses             : 6
% 0.19/0.45  #    Non-unit-clauses                  : 310
% 0.19/0.45  # Current number of unprocessed clauses: 2274
% 0.19/0.45  # ...number of literals in the above   : 7480
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 57
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 12281
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 10204
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 602
% 0.19/0.45  # Unit Clause-clause subsumption calls : 230
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 78
% 0.19/0.45  # BW rewrite match successes           : 7
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 66352
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.113 s
% 0.19/0.45  # System time              : 0.005 s
% 0.19/0.45  # Total time               : 0.118 s
% 0.19/0.45  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
