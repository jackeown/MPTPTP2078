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
% DateTime   : Thu Dec  3 10:57:01 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 203 expanded)
%              Number of clauses        :   24 (  90 expanded)
%              Number of leaves         :    7 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :   96 ( 622 expanded)
%              Number of equality atoms :    8 (  76 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
     => ~ ( r2_hidden(X1,X4)
          & ! [X5,X6] :
              ~ ( X1 = k4_tarski(X5,X6)
                & r2_hidden(X5,X2)
                & r2_hidden(X6,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
       => ~ ( r2_hidden(X1,X4)
            & ! [X5,X6] :
                ~ ( X1 = k4_tarski(X5,X6)
                  & r2_hidden(X5,X2)
                  & r2_hidden(X6,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_relset_1])).

fof(c_0_8,plain,(
    ! [X77,X78,X79] :
      ( ~ r2_hidden(X77,X78)
      | ~ m1_subset_1(X78,k1_zfmisc_1(X79))
      | m1_subset_1(X77,X79) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_9,negated_conjecture,(
    ! [X84,X85] :
      ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & r2_hidden(esk4_0,esk7_0)
      & ( esk4_0 != k4_tarski(X84,X85)
        | ~ r2_hidden(X84,esk5_0)
        | ~ r2_hidden(X85,esk6_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

cnf(c_0_10,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X73,X74] :
      ( ~ m1_subset_1(X73,X74)
      | v1_xboole_0(X74)
      | r2_hidden(X73,X74) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(esk5_0,esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk4_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X69,X70] :
      ( ~ v1_xboole_0(X69)
      | ~ m1_subset_1(X70,k1_zfmisc_1(X69))
      | v1_xboole_0(X70) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_16,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0))
    | r2_hidden(esk4_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_20,plain,(
    ! [X24,X25] :
      ( ~ r2_hidden(X24,X25)
      | ~ v1_xboole_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_21,negated_conjecture,
    ( v1_xboole_0(X1)
    | r2_hidden(esk4_0,k2_zfmisc_1(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | r2_hidden(esk4_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_11])).

fof(c_0_24,plain,(
    ! [X58,X59,X60] :
      ( ~ r2_hidden(X58,k2_zfmisc_1(X59,X60))
      | k4_tarski(esk2_1(X58),esk3_1(X58)) = X58 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk4_0,k2_zfmisc_1(esk5_0,esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_26,plain,(
    ! [X65,X66,X67,X68] :
      ( ( r2_hidden(X65,X67)
        | ~ r2_hidden(k4_tarski(X65,X66),k2_zfmisc_1(X67,X68)) )
      & ( r2_hidden(X66,X68)
        | ~ r2_hidden(k4_tarski(X65,X66),k2_zfmisc_1(X67,X68)) )
      & ( ~ r2_hidden(X65,X67)
        | ~ r2_hidden(X66,X68)
        | r2_hidden(k4_tarski(X65,X66),k2_zfmisc_1(X67,X68)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_27,plain,
    ( k4_tarski(esk2_1(X1),esk3_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk4_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_14])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( k4_tarski(esk2_1(esk4_0),esk3_1(esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( esk4_0 != k4_tarski(X1,X2)
    | ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X2,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),X1)
    | ~ r2_hidden(esk4_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(esk3_1(esk4_0),esk6_0)
    | ~ r2_hidden(esk2_1(esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk3_1(esk4_0),X1)
    | ~ r2_hidden(esk4_0,k2_zfmisc_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(esk3_1(esk4_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:09 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.35  # No SInE strategy applied
% 0.19/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.38  # and selection function SelectNegativeLiterals.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t6_relset_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>~((r2_hidden(X1,X4)&![X5, X6]:~(((X1=k4_tarski(X5,X6)&r2_hidden(X5,X2))&r2_hidden(X6,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 0.19/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.38  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.19/0.38  fof(t7_boole, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 0.19/0.38  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 0.19/0.38  fof(t106_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 0.19/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>~((r2_hidden(X1,X4)&![X5, X6]:~(((X1=k4_tarski(X5,X6)&r2_hidden(X5,X2))&r2_hidden(X6,X3))))))), inference(assume_negation,[status(cth)],[t6_relset_1])).
% 0.19/0.38  fof(c_0_8, plain, ![X77, X78, X79]:(~r2_hidden(X77,X78)|~m1_subset_1(X78,k1_zfmisc_1(X79))|m1_subset_1(X77,X79)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.38  fof(c_0_9, negated_conjecture, ![X84, X85]:(m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))&(r2_hidden(esk4_0,esk7_0)&(esk4_0!=k4_tarski(X84,X85)|~r2_hidden(X84,esk5_0)|~r2_hidden(X85,esk6_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.19/0.38  cnf(c_0_10, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  fof(c_0_12, plain, ![X73, X74]:(~m1_subset_1(X73,X74)|(v1_xboole_0(X74)|r2_hidden(X73,X74))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.38  cnf(c_0_13, negated_conjecture, (m1_subset_1(X1,k2_zfmisc_1(esk5_0,esk6_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.38  cnf(c_0_14, negated_conjecture, (r2_hidden(esk4_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  fof(c_0_15, plain, ![X69, X70]:(~v1_xboole_0(X69)|(~m1_subset_1(X70,k1_zfmisc_1(X69))|v1_xboole_0(X70))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.19/0.38  cnf(c_0_16, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.38  cnf(c_0_18, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0))|r2_hidden(esk4_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.38  fof(c_0_20, plain, ![X24, X25]:(~r2_hidden(X24,X25)|~v1_xboole_0(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (v1_xboole_0(X1)|r2_hidden(esk4_0,k2_zfmisc_1(esk5_0,esk6_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.38  cnf(c_0_22, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (v1_xboole_0(esk7_0)|r2_hidden(esk4_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_21, c_0_11])).
% 0.19/0.38  fof(c_0_24, plain, ![X58, X59, X60]:(~r2_hidden(X58,k2_zfmisc_1(X59,X60))|k4_tarski(esk2_1(X58),esk3_1(X58))=X58), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(esk4_0,k2_zfmisc_1(esk5_0,esk6_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.38  fof(c_0_26, plain, ![X65, X66, X67, X68]:(((r2_hidden(X65,X67)|~r2_hidden(k4_tarski(X65,X66),k2_zfmisc_1(X67,X68)))&(r2_hidden(X66,X68)|~r2_hidden(k4_tarski(X65,X66),k2_zfmisc_1(X67,X68))))&(~r2_hidden(X65,X67)|~r2_hidden(X66,X68)|r2_hidden(k4_tarski(X65,X66),k2_zfmisc_1(X67,X68)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).
% 0.19/0.38  cnf(c_0_27, plain, (k4_tarski(esk2_1(X1),esk3_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk4_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_25, c_0_14])).
% 0.19/0.38  cnf(c_0_29, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (k4_tarski(esk2_1(esk4_0),esk3_1(esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (esk4_0!=k4_tarski(X1,X2)|~r2_hidden(X1,esk5_0)|~r2_hidden(X2,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(esk2_1(esk4_0),X1)|~r2_hidden(esk4_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.38  cnf(c_0_33, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (~r2_hidden(esk3_1(esk4_0),esk6_0)|~r2_hidden(esk2_1(esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(esk2_1(esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_28])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (r2_hidden(esk3_1(esk4_0),X1)|~r2_hidden(esk4_0,k2_zfmisc_1(X2,X1))), inference(spm,[status(thm)],[c_0_33, c_0_30])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (~r2_hidden(esk3_1(esk4_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_28]), c_0_37]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 39
% 0.19/0.38  # Proof object clause steps            : 24
% 0.19/0.38  # Proof object formula steps           : 15
% 0.19/0.38  # Proof object conjectures             : 20
% 0.19/0.38  # Proof object clause conjectures      : 17
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 10
% 0.19/0.38  # Proof object initial formulas used   : 7
% 0.19/0.38  # Proof object generating inferences   : 13
% 0.19/0.38  # Proof object simplifying inferences  : 3
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 22
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 35
% 0.19/0.38  # Removed in clause preprocessing      : 8
% 0.19/0.38  # Initial clauses in saturation        : 27
% 0.19/0.38  # Processed clauses                    : 78
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 6
% 0.19/0.38  # ...remaining for further processing  : 72
% 0.19/0.38  # Other redundant clauses eliminated   : 3
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 6
% 0.19/0.38  # Generated clauses                    : 88
% 0.19/0.38  # ...of the previous two non-trivial   : 84
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 85
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 3
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
% 0.19/0.38  # Current number of processed clauses  : 36
% 0.19/0.38  #    Positive orientable unit clauses  : 9
% 0.19/0.38  #    Positive unorientable unit clauses: 1
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 25
% 0.19/0.38  # Current number of unprocessed clauses: 60
% 0.19/0.38  # ...number of literals in the above   : 153
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 41
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 161
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 131
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.19/0.38  # Unit Clause-clause subsumption calls : 15
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 10
% 0.19/0.38  # BW rewrite match successes           : 10
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 3584
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.029 s
% 0.19/0.38  # System time              : 0.007 s
% 0.19/0.38  # Total time               : 0.036 s
% 0.19/0.38  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
