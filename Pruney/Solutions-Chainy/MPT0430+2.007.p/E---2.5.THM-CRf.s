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
% DateTime   : Thu Dec  3 10:48:05 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   47 (  87 expanded)
%              Number of clauses        :   30 (  38 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 278 expanded)
%              Number of equality atoms :   14 (  24 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( ( v3_setfam_1(X2,X1)
              & r1_tarski(X3,X2) )
           => v3_setfam_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_setfam_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d13_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v3_setfam_1(X2,X1)
      <=> ~ r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
           => ( ( v3_setfam_1(X2,X1)
                & r1_tarski(X3,X2) )
             => v3_setfam_1(X3,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t62_setfam_1])).

fof(c_0_9,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | ~ r1_tarski(X16,X17)
      | r1_tarski(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_10,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & v3_setfam_1(esk3_0,esk2_0)
    & r1_tarski(esk4_0,esk3_0)
    & ~ v3_setfam_1(esk4_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X18,X19] : r1_tarski(k4_xboole_0(X18,X19),X18) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_14,plain,(
    ! [X20,X21] :
      ( v1_xboole_0(X21)
      | ~ r1_tarski(X21,X20)
      | ~ r1_xboole_0(X21,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_18,plain,(
    ! [X24,X25] :
      ( ( ~ v3_setfam_1(X25,X24)
        | ~ r2_hidden(X24,X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))) )
      & ( r2_hidden(X24,X25)
        | v3_setfam_1(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_setfam_1])])])])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk4_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_21,plain,(
    ! [X22,X23] : r1_xboole_0(k4_xboole_0(X22,X23),X23) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | v3_setfam_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( ~ v3_setfam_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_26,plain,(
    ! [X14] :
      ( ~ v1_xboole_0(X14)
      | X14 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_27,negated_conjecture,
    ( v1_xboole_0(k4_xboole_0(esk4_0,X1))
    | ~ r1_xboole_0(k4_xboole_0(esk4_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( v1_xboole_0(k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_16])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( v1_xboole_0(k4_xboole_0(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( ~ v3_setfam_1(X1,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,negated_conjecture,
    ( v3_setfam_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( v1_xboole_0(k4_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk2_0,k4_xboole_0(esk4_0,X1))
    | r2_hidden(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k4_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_32])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.10  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.09/0.30  % Computer   : n006.cluster.edu
% 0.09/0.30  % Model      : x86_64 x86_64
% 0.09/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.30  % Memory     : 8042.1875MB
% 0.09/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.30  % CPULimit   : 60
% 0.09/0.30  % WCLimit    : 600
% 0.09/0.30  % DateTime   : Tue Dec  1 16:33:52 EST 2020
% 0.09/0.30  % CPUTime    : 
% 0.09/0.30  # Version: 2.5pre002
% 0.09/0.30  # No SInE strategy applied
% 0.09/0.30  # Trying AutoSched0 for 299 seconds
% 0.15/0.32  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074I
% 0.15/0.32  # and selection function SelectCQIArEqFirst.
% 0.15/0.32  #
% 0.15/0.32  # Preprocessing time       : 0.013 s
% 0.15/0.32  # Presaturation interreduction done
% 0.15/0.32  
% 0.15/0.32  # Proof found!
% 0.15/0.32  # SZS status Theorem
% 0.15/0.32  # SZS output start CNFRefutation
% 0.15/0.32  fof(t62_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((v3_setfam_1(X2,X1)&r1_tarski(X3,X2))=>v3_setfam_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_setfam_1)).
% 0.15/0.32  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.15/0.32  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.15/0.32  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.15/0.32  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.15/0.32  fof(d13_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v3_setfam_1(X2,X1)<=>~(r2_hidden(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_setfam_1)).
% 0.15/0.32  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.15/0.32  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.15/0.32  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((v3_setfam_1(X2,X1)&r1_tarski(X3,X2))=>v3_setfam_1(X3,X1))))), inference(assume_negation,[status(cth)],[t62_setfam_1])).
% 0.15/0.32  fof(c_0_9, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|~r1_tarski(X16,X17)|r1_tarski(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.15/0.32  fof(c_0_10, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&((v3_setfam_1(esk3_0,esk2_0)&r1_tarski(esk4_0,esk3_0))&~v3_setfam_1(esk4_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.15/0.32  cnf(c_0_11, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.32  cnf(c_0_12, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.32  fof(c_0_13, plain, ![X18, X19]:r1_tarski(k4_xboole_0(X18,X19),X18), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.15/0.32  fof(c_0_14, plain, ![X20, X21]:(v1_xboole_0(X21)|(~r1_tarski(X21,X20)|~r1_xboole_0(X21,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.15/0.32  cnf(c_0_15, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.15/0.32  cnf(c_0_16, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.32  fof(c_0_17, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.15/0.32  fof(c_0_18, plain, ![X24, X25]:((~v3_setfam_1(X25,X24)|~r2_hidden(X24,X25)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))))&(r2_hidden(X24,X25)|v3_setfam_1(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_setfam_1])])])])).
% 0.15/0.32  cnf(c_0_19, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.32  cnf(c_0_20, negated_conjecture, (r1_tarski(k4_xboole_0(esk4_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.15/0.32  fof(c_0_21, plain, ![X22, X23]:r1_xboole_0(k4_xboole_0(X22,X23),X23), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.15/0.32  cnf(c_0_22, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.32  cnf(c_0_23, plain, (r2_hidden(X1,X2)|v3_setfam_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.32  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.32  cnf(c_0_25, negated_conjecture, (~v3_setfam_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.32  fof(c_0_26, plain, ![X14]:(~v1_xboole_0(X14)|X14=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.15/0.32  cnf(c_0_27, negated_conjecture, (v1_xboole_0(k4_xboole_0(esk4_0,X1))|~r1_xboole_0(k4_xboole_0(esk4_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.15/0.32  cnf(c_0_28, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.15/0.32  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.32  cnf(c_0_30, plain, (v1_xboole_0(k4_xboole_0(X1,X2))|~r1_xboole_0(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_19, c_0_16])).
% 0.15/0.32  cnf(c_0_31, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_22])).
% 0.15/0.32  cnf(c_0_32, negated_conjecture, (r2_hidden(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.15/0.32  cnf(c_0_33, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.15/0.32  cnf(c_0_34, negated_conjecture, (v1_xboole_0(k4_xboole_0(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.15/0.32  cnf(c_0_35, plain, (~v3_setfam_1(X1,X2)|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.32  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.32  cnf(c_0_37, negated_conjecture, (v3_setfam_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.32  cnf(c_0_38, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_29])).
% 0.15/0.32  cnf(c_0_39, plain, (v1_xboole_0(k4_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_30, c_0_28])).
% 0.15/0.32  cnf(c_0_40, negated_conjecture, (r2_hidden(esk2_0,k4_xboole_0(esk4_0,X1))|r2_hidden(esk2_0,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.15/0.32  cnf(c_0_41, negated_conjecture, (k4_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.15/0.32  cnf(c_0_42, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.15/0.32  cnf(c_0_43, negated_conjecture, (~r2_hidden(esk2_0,k4_xboole_0(X1,esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_32])).
% 0.15/0.32  cnf(c_0_44, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_39])).
% 0.15/0.32  cnf(c_0_45, negated_conjecture, (r2_hidden(esk2_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.15/0.32  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])]), ['proof']).
% 0.15/0.32  # SZS output end CNFRefutation
% 0.15/0.32  # Proof object total steps             : 47
% 0.15/0.32  # Proof object clause steps            : 30
% 0.15/0.32  # Proof object formula steps           : 17
% 0.15/0.32  # Proof object conjectures             : 19
% 0.15/0.32  # Proof object clause conjectures      : 16
% 0.15/0.32  # Proof object formula conjectures     : 3
% 0.15/0.32  # Proof object initial clauses used    : 14
% 0.15/0.32  # Proof object initial formulas used   : 8
% 0.15/0.32  # Proof object generating inferences   : 14
% 0.15/0.32  # Proof object simplifying inferences  : 8
% 0.15/0.32  # Training examples: 0 positive, 0 negative
% 0.15/0.32  # Parsed axioms                        : 8
% 0.15/0.32  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.32  # Initial clauses                      : 18
% 0.15/0.32  # Removed in clause preprocessing      : 0
% 0.15/0.32  # Initial clauses in saturation        : 18
% 0.15/0.32  # Processed clauses                    : 101
% 0.15/0.32  # ...of these trivial                  : 7
% 0.15/0.32  # ...subsumed                          : 15
% 0.15/0.32  # ...remaining for further processing  : 79
% 0.15/0.32  # Other redundant clauses eliminated   : 3
% 0.15/0.32  # Clauses deleted for lack of memory   : 0
% 0.15/0.32  # Backward-subsumed                    : 0
% 0.15/0.32  # Backward-rewritten                   : 2
% 0.15/0.32  # Generated clauses                    : 141
% 0.15/0.32  # ...of the previous two non-trivial   : 100
% 0.15/0.32  # Contextual simplify-reflections      : 0
% 0.15/0.32  # Paramodulations                      : 136
% 0.15/0.32  # Factorizations                       : 2
% 0.15/0.32  # Equation resolutions                 : 3
% 0.15/0.32  # Propositional unsat checks           : 0
% 0.15/0.32  #    Propositional check models        : 0
% 0.15/0.32  #    Propositional check unsatisfiable : 0
% 0.15/0.32  #    Propositional clauses             : 0
% 0.15/0.32  #    Propositional clauses after purity: 0
% 0.15/0.32  #    Propositional unsat core size     : 0
% 0.15/0.32  #    Propositional preprocessing time  : 0.000
% 0.15/0.32  #    Propositional encoding time       : 0.000
% 0.15/0.32  #    Propositional solver time         : 0.000
% 0.15/0.32  #    Success case prop preproc time    : 0.000
% 0.15/0.32  #    Success case prop encoding time   : 0.000
% 0.15/0.32  #    Success case prop solver time     : 0.000
% 0.15/0.32  # Current number of processed clauses  : 56
% 0.15/0.32  #    Positive orientable unit clauses  : 18
% 0.15/0.32  #    Positive unorientable unit clauses: 0
% 0.15/0.32  #    Negative unit clauses             : 4
% 0.15/0.32  #    Non-unit-clauses                  : 34
% 0.15/0.32  # Current number of unprocessed clauses: 30
% 0.15/0.32  # ...number of literals in the above   : 85
% 0.15/0.32  # Current number of archived formulas  : 0
% 0.15/0.32  # Current number of archived clauses   : 20
% 0.15/0.32  # Clause-clause subsumption calls (NU) : 260
% 0.15/0.32  # Rec. Clause-clause subsumption calls : 214
% 0.15/0.32  # Non-unit clause-clause subsumptions  : 13
% 0.15/0.32  # Unit Clause-clause subsumption calls : 60
% 0.15/0.32  # Rewrite failures with RHS unbound    : 0
% 0.15/0.32  # BW rewrite match attempts            : 24
% 0.15/0.32  # BW rewrite match successes           : 2
% 0.15/0.32  # Condensation attempts                : 0
% 0.15/0.32  # Condensation successes               : 0
% 0.15/0.32  # Termbank termtop insertions          : 2763
% 0.15/0.32  
% 0.15/0.32  # -------------------------------------------------
% 0.15/0.32  # User time                : 0.016 s
% 0.15/0.32  # System time              : 0.001 s
% 0.15/0.32  # Total time               : 0.017 s
% 0.15/0.32  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
