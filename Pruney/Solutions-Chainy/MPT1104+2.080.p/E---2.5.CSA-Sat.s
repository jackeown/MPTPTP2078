%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:59 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 129 expanded)
%              Number of clauses        :   24 (  48 expanded)
%              Number of leaves         :    6 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   69 ( 464 expanded)
%              Number of equality atoms :   32 ( 167 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_pre_topc,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( k2_struct_0(X1) = k4_subset_1(u1_struct_0(X1),X2,X3)
                  & r1_xboole_0(X2,X3) )
               => X3 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_pre_topc)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t88_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( k2_struct_0(X1) = k4_subset_1(u1_struct_0(X1),X2,X3)
                    & r1_xboole_0(X2,X3) )
                 => X3 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_pre_topc])).

fof(c_0_7,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | ~ m1_subset_1(X12,k1_zfmisc_1(X10))
      | k4_subset_1(X10,X11,X12) = k2_xboole_0(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_8,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & k2_struct_0(esk1_0) = k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)
    & r1_xboole_0(esk2_0,esk3_0)
    & esk3_0 != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_9,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

fof(c_0_11,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_12,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,esk3_0) = k2_xboole_0(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( k2_struct_0(esk1_0) = k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_16,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | k7_subset_1(X13,X14,X15) = k4_xboole_0(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_17,plain,(
    ! [X8,X9] :
      ( ~ r1_xboole_0(X8,X9)
      | k4_xboole_0(k2_xboole_0(X8,X9),X9) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( esk3_0 != k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( k2_struct_0(esk1_0) = k2_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,esk2_0) = k2_xboole_0(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_13]),
    [final]).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_24,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_25,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_xboole_0(esk2_0,esk3_0),esk2_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_20,c_0_21]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0) = k2_xboole_0(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_13]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk3_0,esk2_0) = k2_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_10]),c_0_23]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0) = k2_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_21]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk3_0,esk3_0) = k2_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_10]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_13]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1) = k4_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_10]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk2_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_23]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk3_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_19]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S076I
% 0.13/0.37  # and selection function SelectCQIAr.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # No proof found!
% 0.13/0.37  # SZS status CounterSatisfiable
% 0.13/0.37  # SZS output start Saturation
% 0.13/0.37  fof(t25_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_struct_0(X1)=k4_subset_1(u1_struct_0(X1),X2,X3)&r1_xboole_0(X2,X3))=>X3=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_pre_topc)).
% 0.13/0.37  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.13/0.37  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.13/0.37  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.13/0.37  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.13/0.37  fof(t88_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 0.13/0.37  fof(c_0_6, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((k2_struct_0(X1)=k4_subset_1(u1_struct_0(X1),X2,X3)&r1_xboole_0(X2,X3))=>X3=k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t25_pre_topc])).
% 0.13/0.37  fof(c_0_7, plain, ![X10, X11, X12]:(~m1_subset_1(X11,k1_zfmisc_1(X10))|~m1_subset_1(X12,k1_zfmisc_1(X10))|k4_subset_1(X10,X11,X12)=k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.13/0.37  fof(c_0_8, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((k2_struct_0(esk1_0)=k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)&r1_xboole_0(esk2_0,esk3_0))&esk3_0!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.13/0.37  cnf(c_0_9, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.37  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.37  fof(c_0_11, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,esk3_0)=k2_xboole_0(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_9, c_0_10]), ['final']).
% 0.13/0.37  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (k2_struct_0(esk1_0)=k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  fof(c_0_15, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.13/0.37  fof(c_0_16, plain, ![X13, X14, X15]:(~m1_subset_1(X14,k1_zfmisc_1(X13))|k7_subset_1(X13,X14,X15)=k4_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.13/0.37  fof(c_0_17, plain, ![X8, X9]:(~r1_xboole_0(X8,X9)|k4_xboole_0(k2_xboole_0(X8,X9),X9)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).
% 0.13/0.37  cnf(c_0_18, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (esk3_0!=k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (k2_struct_0(esk1_0)=k2_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), ['final']).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,esk2_0)=k2_xboole_0(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_9, c_0_13]), ['final']).
% 0.13/0.37  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.37  cnf(c_0_24, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.13/0.37  cnf(c_0_25, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_18, c_0_19]), ['final']).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_xboole_0(esk2_0,esk3_0),esk2_0)!=esk3_0), inference(rw,[status(thm)],[c_0_20, c_0_21]), ['final']).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0)=k2_xboole_0(esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_22, c_0_13]), ['final']).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk3_0,esk2_0)=k2_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_10]), c_0_23]), ['final']).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)=k2_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_14, c_0_21]), ['final']).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk3_0,esk3_0)=k2_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_12, c_0_10]), ['final']).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_13]), ['final']).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk3_0,X1)=k4_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_10]), ['final']).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk2_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_23]), ['final']).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),esk3_0)=esk2_0), inference(spm,[status(thm)],[c_0_25, c_0_19]), ['final']).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.37  # SZS output end Saturation
% 0.13/0.37  # Proof object total steps             : 37
% 0.13/0.37  # Proof object clause steps            : 24
% 0.13/0.37  # Proof object formula steps           : 13
% 0.13/0.37  # Proof object conjectures             : 22
% 0.13/0.37  # Proof object clause conjectures      : 19
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 11
% 0.13/0.37  # Proof object initial formulas used   : 6
% 0.13/0.37  # Proof object generating inferences   : 11
% 0.13/0.37  # Proof object simplifying inferences  : 5
% 0.13/0.37  # Parsed axioms                        : 6
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 11
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 11
% 0.13/0.37  # Processed clauses                    : 35
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 35
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 2
% 0.13/0.37  # Generated clauses                    : 12
% 0.13/0.37  # ...of the previous two non-trivial   : 13
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 12
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 22
% 0.13/0.37  #    Positive orientable unit clauses  : 14
% 0.13/0.37  #    Positive unorientable unit clauses: 1
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 6
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 13
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 1
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 5
% 0.13/0.37  # BW rewrite match successes           : 3
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 863
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.029 s
% 0.13/0.37  # System time              : 0.002 s
% 0.13/0.37  # Total time               : 0.031 s
% 0.13/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
