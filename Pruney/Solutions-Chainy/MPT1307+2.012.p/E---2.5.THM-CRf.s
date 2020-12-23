%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:13 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   32 (  54 expanded)
%              Number of clauses        :   19 (  22 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 167 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( v2_tops_2(X2,X1)
               => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tops_2)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t19_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( ( r1_tarski(X2,X3)
                  & v2_tops_2(X3,X1) )
               => v2_tops_2(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ( v2_tops_2(X2,X1)
                 => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_tops_2])).

fof(c_0_7,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | k7_subset_1(X9,X10,X11) = k4_xboole_0(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_8,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & v2_tops_2(esk2_0,esk1_0)
    & ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X14,X15,X16] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
      | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
      | ~ r1_tarski(X15,X16)
      | ~ v2_tops_2(X16,X14)
      | v2_tops_2(X15,X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_tops_2])])])).

cnf(c_0_10,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( v2_tops_2(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X3)
    | ~ v2_tops_2(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,X1) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v2_tops_2(X1,esk1_0)
    | ~ v2_tops_2(X2,esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v2_tops_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_18,plain,(
    ! [X7,X8] : r1_tarski(k4_xboole_0(X7,X8),X7) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_19,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X12,k1_zfmisc_1(X13))
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | m1_subset_1(X12,k1_zfmisc_1(X13)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_tops_2(k4_xboole_0(esk2_0,esk3_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v2_tops_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_11])])).

cnf(c_0_22,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X5,X6)
      | r1_tarski(X4,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( ~ m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n007.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 12:20:06 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.18/0.34  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S050I
% 0.18/0.34  # and selection function PSelectNewComplexExceptUniqMaxHorn.
% 0.18/0.34  #
% 0.18/0.34  # Preprocessing time       : 0.015 s
% 0.18/0.34  # Presaturation interreduction done
% 0.18/0.34  
% 0.18/0.34  # Proof found!
% 0.18/0.34  # SZS status Theorem
% 0.18/0.34  # SZS output start CNFRefutation
% 0.18/0.34  fof(t25_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tops_2(X2,X1)=>v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tops_2)).
% 0.18/0.34  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.18/0.34  fof(t19_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>((r1_tarski(X2,X3)&v2_tops_2(X3,X1))=>v2_tops_2(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tops_2)).
% 0.18/0.34  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.18/0.34  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.34  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.18/0.34  fof(c_0_6, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tops_2(X2,X1)=>v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t25_tops_2])).
% 0.18/0.34  fof(c_0_7, plain, ![X9, X10, X11]:(~m1_subset_1(X10,k1_zfmisc_1(X9))|k7_subset_1(X9,X10,X11)=k4_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.18/0.34  fof(c_0_8, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))&(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))&(v2_tops_2(esk2_0,esk1_0)&~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.18/0.34  fof(c_0_9, plain, ![X14, X15, X16]:(~l1_pre_topc(X14)|(~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|(~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|(~r1_tarski(X15,X16)|~v2_tops_2(X16,X14)|v2_tops_2(X15,X14))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_tops_2])])])).
% 0.18/0.34  cnf(c_0_10, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.34  cnf(c_0_12, plain, (v2_tops_2(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~r1_tarski(X2,X3)|~v2_tops_2(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.34  cnf(c_0_13, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.34  cnf(c_0_14, negated_conjecture, (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.34  cnf(c_0_15, negated_conjecture, (k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,X1)=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.18/0.34  cnf(c_0_16, negated_conjecture, (v2_tops_2(X1,esk1_0)|~v2_tops_2(X2,esk1_0)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.18/0.34  cnf(c_0_17, negated_conjecture, (v2_tops_2(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.34  fof(c_0_18, plain, ![X7, X8]:r1_tarski(k4_xboole_0(X7,X8),X7), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.18/0.34  fof(c_0_19, plain, ![X12, X13]:((~m1_subset_1(X12,k1_zfmisc_1(X13))|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|m1_subset_1(X12,k1_zfmisc_1(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.34  cnf(c_0_20, negated_conjecture, (~v2_tops_2(k4_xboole_0(esk2_0,esk3_0),esk1_0)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.18/0.34  cnf(c_0_21, negated_conjecture, (v2_tops_2(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_11])])).
% 0.18/0.34  cnf(c_0_22, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.34  fof(c_0_23, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|~r1_tarski(X5,X6)|r1_tarski(X4,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.18/0.34  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.34  cnf(c_0_25, negated_conjecture, (~m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.18/0.34  cnf(c_0_26, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.34  cnf(c_0_27, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.34  cnf(c_0_28, negated_conjecture, (r1_tarski(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_24, c_0_11])).
% 0.18/0.34  cnf(c_0_29, negated_conjecture, (~r1_tarski(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.34  cnf(c_0_30, negated_conjecture, (r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.18/0.34  cnf(c_0_31, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_22])]), ['proof']).
% 0.18/0.34  # SZS output end CNFRefutation
% 0.18/0.34  # Proof object total steps             : 32
% 0.18/0.34  # Proof object clause steps            : 19
% 0.18/0.34  # Proof object formula steps           : 13
% 0.18/0.34  # Proof object conjectures             : 16
% 0.18/0.34  # Proof object clause conjectures      : 13
% 0.18/0.34  # Proof object formula conjectures     : 3
% 0.18/0.34  # Proof object initial clauses used    : 10
% 0.18/0.34  # Proof object initial formulas used   : 6
% 0.18/0.34  # Proof object generating inferences   : 8
% 0.18/0.34  # Proof object simplifying inferences  : 7
% 0.18/0.34  # Training examples: 0 positive, 0 negative
% 0.18/0.34  # Parsed axioms                        : 6
% 0.18/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.34  # Initial clauses                      : 11
% 0.18/0.34  # Removed in clause preprocessing      : 0
% 0.18/0.34  # Initial clauses in saturation        : 11
% 0.18/0.34  # Processed clauses                    : 41
% 0.18/0.34  # ...of these trivial                  : 0
% 0.18/0.34  # ...subsumed                          : 0
% 0.18/0.34  # ...remaining for further processing  : 41
% 0.18/0.34  # Other redundant clauses eliminated   : 0
% 0.18/0.34  # Clauses deleted for lack of memory   : 0
% 0.18/0.34  # Backward-subsumed                    : 0
% 0.18/0.34  # Backward-rewritten                   : 1
% 0.18/0.34  # Generated clauses                    : 37
% 0.18/0.34  # ...of the previous two non-trivial   : 34
% 0.18/0.34  # Contextual simplify-reflections      : 0
% 0.18/0.34  # Paramodulations                      : 37
% 0.18/0.34  # Factorizations                       : 0
% 0.18/0.34  # Equation resolutions                 : 0
% 0.18/0.34  # Propositional unsat checks           : 0
% 0.18/0.34  #    Propositional check models        : 0
% 0.18/0.34  #    Propositional check unsatisfiable : 0
% 0.18/0.34  #    Propositional clauses             : 0
% 0.18/0.34  #    Propositional clauses after purity: 0
% 0.18/0.34  #    Propositional unsat core size     : 0
% 0.18/0.34  #    Propositional preprocessing time  : 0.000
% 0.18/0.34  #    Propositional encoding time       : 0.000
% 0.18/0.34  #    Propositional solver time         : 0.000
% 0.18/0.34  #    Success case prop preproc time    : 0.000
% 0.18/0.34  #    Success case prop encoding time   : 0.000
% 0.18/0.34  #    Success case prop solver time     : 0.000
% 0.18/0.34  # Current number of processed clauses  : 29
% 0.18/0.34  #    Positive orientable unit clauses  : 10
% 0.18/0.34  #    Positive unorientable unit clauses: 0
% 0.18/0.34  #    Negative unit clauses             : 3
% 0.18/0.34  #    Non-unit-clauses                  : 16
% 0.18/0.34  # Current number of unprocessed clauses: 14
% 0.18/0.34  # ...number of literals in the above   : 21
% 0.18/0.34  # Current number of archived formulas  : 0
% 0.18/0.34  # Current number of archived clauses   : 12
% 0.18/0.34  # Clause-clause subsumption calls (NU) : 88
% 0.18/0.34  # Rec. Clause-clause subsumption calls : 54
% 0.18/0.34  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.34  # Unit Clause-clause subsumption calls : 4
% 0.18/0.34  # Rewrite failures with RHS unbound    : 0
% 0.18/0.34  # BW rewrite match attempts            : 1
% 0.18/0.34  # BW rewrite match successes           : 1
% 0.18/0.34  # Condensation attempts                : 0
% 0.18/0.34  # Condensation successes               : 0
% 0.18/0.34  # Termbank termtop insertions          : 1366
% 0.18/0.34  
% 0.18/0.34  # -------------------------------------------------
% 0.18/0.34  # User time                : 0.013 s
% 0.18/0.34  # System time              : 0.006 s
% 0.18/0.34  # Total time               : 0.019 s
% 0.18/0.34  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
