%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:18 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   37 (  76 expanded)
%              Number of clauses        :   22 (  33 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  123 ( 329 expanded)
%              Number of equality atoms :   27 (  51 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t48_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
             => ! [X4] :
                  ( r2_hidden(X4,k2_relset_1(X2,X1,X3))
                <=> ? [X5] :
                      ( m1_subset_1(X5,X2)
                      & r2_hidden(k4_tarski(X5,X4),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(c_0_7,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | m1_subset_1(k1_relset_1(X31,X32,X33),k1_zfmisc_1(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

fof(c_0_8,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k1_relset_1(X34,X35,X36) = k1_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
               => ! [X4] :
                    ( r2_hidden(X4,k2_relset_1(X2,X1,X3))
                  <=> ? [X5] :
                        ( m1_subset_1(X5,X2)
                        & r2_hidden(k4_tarski(X5,X4),X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_relset_1])).

cnf(c_0_10,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,(
    ! [X44] :
      ( ~ v1_xboole_0(esk7_0)
      & ~ v1_xboole_0(esk8_0)
      & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0)))
      & ( ~ r2_hidden(esk10_0,k2_relset_1(esk8_0,esk7_0,esk9_0))
        | ~ m1_subset_1(X44,esk8_0)
        | ~ r2_hidden(k4_tarski(X44,esk10_0),esk9_0) )
      & ( m1_subset_1(esk11_0,esk8_0)
        | r2_hidden(esk10_0,k2_relset_1(esk8_0,esk7_0,esk9_0)) )
      & ( r2_hidden(k4_tarski(esk11_0,esk10_0),esk9_0)
        | r2_hidden(esk10_0,k2_relset_1(esk8_0,esk7_0,esk9_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).

fof(c_0_13,plain,(
    ! [X6,X7,X8] :
      ( ~ r2_hidden(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8))
      | m1_subset_1(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_14,plain,
    ( m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X9,X10,X11,X13,X14,X15,X16,X18] :
      ( ( ~ r2_hidden(X11,X10)
        | r2_hidden(k4_tarski(X11,esk1_3(X9,X10,X11)),X9)
        | X10 != k1_relat_1(X9) )
      & ( ~ r2_hidden(k4_tarski(X13,X14),X9)
        | r2_hidden(X13,X10)
        | X10 != k1_relat_1(X9) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | ~ r2_hidden(k4_tarski(esk2_2(X15,X16),X18),X15)
        | X16 = k1_relat_1(X15) )
      & ( r2_hidden(esk2_2(X15,X16),X16)
        | r2_hidden(k4_tarski(esk2_2(X15,X16),esk3_2(X15,X16)),X15)
        | X16 = k1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_17,plain,(
    ! [X20,X21,X22,X24,X25,X26,X27,X29] :
      ( ( ~ r2_hidden(X22,X21)
        | r2_hidden(k4_tarski(esk4_3(X20,X21,X22),X22),X20)
        | X21 != k2_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X25,X24),X20)
        | r2_hidden(X24,X21)
        | X21 != k2_relat_1(X20) )
      & ( ~ r2_hidden(esk5_2(X26,X27),X27)
        | ~ r2_hidden(k4_tarski(X29,esk5_2(X26,X27)),X26)
        | X27 = k2_relat_1(X26) )
      & ( r2_hidden(esk5_2(X26,X27),X27)
        | r2_hidden(k4_tarski(esk6_2(X26,X27),esk5_2(X26,X27)),X26)
        | X27 = k2_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk9_0),k1_zfmisc_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(esk11_0,esk10_0),esk9_0)
    | r2_hidden(esk10_0,k2_relset_1(esk8_0,esk7_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(esk10_0,k2_relset_1(esk8_0,esk7_0,esk9_0))
    | ~ m1_subset_1(X1,esk8_0)
    | ~ r2_hidden(k4_tarski(X1,esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(X1,esk8_0)
    | ~ r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X4)
    | X4 != k1_relat_1(X1)
    | X2 != k2_relat_1(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk10_0,k2_relset_1(esk8_0,esk7_0,esk9_0))
    | r2_hidden(esk10_0,X1)
    | X1 != k2_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_28,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k2_relset_1(X37,X38,X39) = k2_relat_1(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_29,negated_conjecture,
    ( X1 != k2_relat_1(esk9_0)
    | ~ m1_subset_1(esk4_3(esk9_0,X1,esk10_0),esk8_0)
    | ~ r2_hidden(esk10_0,k2_relset_1(esk8_0,esk7_0,esk9_0))
    | ~ r2_hidden(esk10_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk4_3(X1,X2,X3),esk8_0)
    | k1_relat_1(esk9_0) != k1_relat_1(X1)
    | X2 != k2_relat_1(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk10_0,k2_relset_1(esk8_0,esk7_0,esk9_0))
    | r2_hidden(esk10_0,k2_relat_1(esk9_0)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( X1 != k2_relat_1(esk9_0)
    | ~ r2_hidden(esk10_0,k2_relset_1(esk8_0,esk7_0,esk9_0))
    | ~ r2_hidden(esk10_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk10_0,k2_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_15])])).

cnf(c_0_35,negated_conjecture,
    ( X1 != k2_relat_1(esk9_0)
    | ~ r2_hidden(esk10_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_32]),c_0_34]),c_0_15])])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_35,c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:18:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.12/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.027 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.12/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.12/0.38  fof(t48_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>![X4]:(r2_hidden(X4,k2_relset_1(X2,X1,X3))<=>?[X5]:(m1_subset_1(X5,X2)&r2_hidden(k4_tarski(X5,X4),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 0.12/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.12/0.38  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.12/0.38  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.12/0.38  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.12/0.38  fof(c_0_7, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|m1_subset_1(k1_relset_1(X31,X32,X33),k1_zfmisc_1(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.12/0.38  fof(c_0_8, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k1_relset_1(X34,X35,X36)=k1_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.12/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>![X4]:(r2_hidden(X4,k2_relset_1(X2,X1,X3))<=>?[X5]:(m1_subset_1(X5,X2)&r2_hidden(k4_tarski(X5,X4),X3))))))), inference(assume_negation,[status(cth)],[t48_relset_1])).
% 0.12/0.38  cnf(c_0_10, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.38  cnf(c_0_11, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  fof(c_0_12, negated_conjecture, ![X44]:(~v1_xboole_0(esk7_0)&(~v1_xboole_0(esk8_0)&(m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0)))&((~r2_hidden(esk10_0,k2_relset_1(esk8_0,esk7_0,esk9_0))|(~m1_subset_1(X44,esk8_0)|~r2_hidden(k4_tarski(X44,esk10_0),esk9_0)))&((m1_subset_1(esk11_0,esk8_0)|r2_hidden(esk10_0,k2_relset_1(esk8_0,esk7_0,esk9_0)))&(r2_hidden(k4_tarski(esk11_0,esk10_0),esk9_0)|r2_hidden(esk10_0,k2_relset_1(esk8_0,esk7_0,esk9_0)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).
% 0.12/0.38  fof(c_0_13, plain, ![X6, X7, X8]:(~r2_hidden(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X8))|m1_subset_1(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.12/0.38  cnf(c_0_14, plain, (m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.38  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  fof(c_0_16, plain, ![X9, X10, X11, X13, X14, X15, X16, X18]:(((~r2_hidden(X11,X10)|r2_hidden(k4_tarski(X11,esk1_3(X9,X10,X11)),X9)|X10!=k1_relat_1(X9))&(~r2_hidden(k4_tarski(X13,X14),X9)|r2_hidden(X13,X10)|X10!=k1_relat_1(X9)))&((~r2_hidden(esk2_2(X15,X16),X16)|~r2_hidden(k4_tarski(esk2_2(X15,X16),X18),X15)|X16=k1_relat_1(X15))&(r2_hidden(esk2_2(X15,X16),X16)|r2_hidden(k4_tarski(esk2_2(X15,X16),esk3_2(X15,X16)),X15)|X16=k1_relat_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.12/0.38  fof(c_0_17, plain, ![X20, X21, X22, X24, X25, X26, X27, X29]:(((~r2_hidden(X22,X21)|r2_hidden(k4_tarski(esk4_3(X20,X21,X22),X22),X20)|X21!=k2_relat_1(X20))&(~r2_hidden(k4_tarski(X25,X24),X20)|r2_hidden(X24,X21)|X21!=k2_relat_1(X20)))&((~r2_hidden(esk5_2(X26,X27),X27)|~r2_hidden(k4_tarski(X29,esk5_2(X26,X27)),X26)|X27=k2_relat_1(X26))&(r2_hidden(esk5_2(X26,X27),X27)|r2_hidden(k4_tarski(esk6_2(X26,X27),esk5_2(X26,X27)),X26)|X27=k2_relat_1(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.12/0.38  cnf(c_0_18, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (m1_subset_1(k1_relat_1(esk9_0),k1_zfmisc_1(esk8_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.38  cnf(c_0_20, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_21, plain, (r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_22, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (r2_hidden(k4_tarski(esk11_0,esk10_0),esk9_0)|r2_hidden(esk10_0,k2_relset_1(esk8_0,esk7_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (~r2_hidden(esk10_0,k2_relset_1(esk8_0,esk7_0,esk9_0))|~m1_subset_1(X1,esk8_0)|~r2_hidden(k4_tarski(X1,esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(X1,esk8_0)|~r2_hidden(X1,k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.38  cnf(c_0_26, plain, (r2_hidden(esk4_3(X1,X2,X3),X4)|X4!=k1_relat_1(X1)|X2!=k2_relat_1(X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(esk10_0,k2_relset_1(esk8_0,esk7_0,esk9_0))|r2_hidden(esk10_0,X1)|X1!=k2_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.38  fof(c_0_28, plain, ![X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k2_relset_1(X37,X38,X39)=k2_relat_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (X1!=k2_relat_1(esk9_0)|~m1_subset_1(esk4_3(esk9_0,X1,esk10_0),esk8_0)|~r2_hidden(esk10_0,k2_relset_1(esk8_0,esk7_0,esk9_0))|~r2_hidden(esk10_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk4_3(X1,X2,X3),esk8_0)|k1_relat_1(esk9_0)!=k1_relat_1(X1)|X2!=k2_relat_1(X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(esk10_0,k2_relset_1(esk8_0,esk7_0,esk9_0))|r2_hidden(esk10_0,k2_relat_1(esk9_0))), inference(er,[status(thm)],[c_0_27])).
% 0.12/0.38  cnf(c_0_32, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (X1!=k2_relat_1(esk9_0)|~r2_hidden(esk10_0,k2_relset_1(esk8_0,esk7_0,esk9_0))|~r2_hidden(esk10_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(esk10_0,k2_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_15])])).
% 0.12/0.38  cnf(c_0_35, negated_conjecture, (X1!=k2_relat_1(esk9_0)|~r2_hidden(esk10_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_32]), c_0_34]), c_0_15])])).
% 0.12/0.38  cnf(c_0_36, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_35, c_0_34]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 37
% 0.12/0.38  # Proof object clause steps            : 22
% 0.12/0.38  # Proof object formula steps           : 15
% 0.12/0.38  # Proof object conjectures             : 16
% 0.12/0.38  # Proof object clause conjectures      : 13
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 10
% 0.12/0.38  # Proof object initial formulas used   : 7
% 0.12/0.38  # Proof object generating inferences   : 12
% 0.12/0.38  # Proof object simplifying inferences  : 5
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 7
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 18
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 18
% 0.12/0.38  # Processed clauses                    : 67
% 0.12/0.38  # ...of these trivial                  : 2
% 0.12/0.38  # ...subsumed                          : 3
% 0.12/0.38  # ...remaining for further processing  : 62
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 2
% 0.12/0.38  # Backward-rewritten                   : 1
% 0.12/0.38  # Generated clauses                    : 58
% 0.12/0.38  # ...of the previous two non-trivial   : 54
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 55
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 3
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 41
% 0.12/0.38  #    Positive orientable unit clauses  : 3
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 2
% 0.12/0.38  #    Non-unit-clauses                  : 36
% 0.12/0.38  # Current number of unprocessed clauses: 23
% 0.12/0.38  # ...number of literals in the above   : 88
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 21
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 135
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 79
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.12/0.38  # Unit Clause-clause subsumption calls : 3
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 1
% 0.12/0.38  # BW rewrite match successes           : 1
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 2746
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.026 s
% 0.12/0.38  # System time              : 0.009 s
% 0.12/0.38  # Total time               : 0.035 s
% 0.12/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
