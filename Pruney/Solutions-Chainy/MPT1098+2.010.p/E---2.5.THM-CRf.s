%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:31 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  52 expanded)
%              Number of clauses        :   17 (  20 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   95 ( 239 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(t33_finset_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( v1_finset_1(X1)
        & r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & ! [X4] :
            ~ ( v1_finset_1(X4)
              & r1_tarski(X4,X2)
              & r1_tarski(X1,k2_zfmisc_1(X4,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_finset_1)).

fof(t32_finset_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( v1_finset_1(X1)
        & r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] :
            ~ ( v1_finset_1(X4)
              & r1_tarski(X4,X2)
              & v1_finset_1(X5)
              & r1_tarski(X5,X3)
              & r1_tarski(X1,k2_zfmisc_1(X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_finset_1)).

fof(c_0_5,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(k2_xboole_0(X6,X7),X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_6,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k2_xboole_0(X9,X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_7,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X11,X12,X13] :
      ( ( r1_tarski(k2_zfmisc_1(X11,X13),k2_zfmisc_1(X12,X13))
        | ~ r1_tarski(X11,X12) )
      & ( r1_tarski(k2_zfmisc_1(X13,X11),k2_zfmisc_1(X13,X12))
        | ~ r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( v1_finset_1(X1)
          & r1_tarski(X1,k2_zfmisc_1(X2,X3))
          & ! [X4] :
              ~ ( v1_finset_1(X4)
                & r1_tarski(X4,X2)
                & r1_tarski(X1,k2_zfmisc_1(X4,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t33_finset_1])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X14,X15,X16] :
      ( ( v1_finset_1(esk1_3(X14,X15,X16))
        | ~ v1_finset_1(X14)
        | ~ r1_tarski(X14,k2_zfmisc_1(X15,X16)) )
      & ( r1_tarski(esk1_3(X14,X15,X16),X15)
        | ~ v1_finset_1(X14)
        | ~ r1_tarski(X14,k2_zfmisc_1(X15,X16)) )
      & ( v1_finset_1(esk2_3(X14,X15,X16))
        | ~ v1_finset_1(X14)
        | ~ r1_tarski(X14,k2_zfmisc_1(X15,X16)) )
      & ( r1_tarski(esk2_3(X14,X15,X16),X16)
        | ~ v1_finset_1(X14)
        | ~ r1_tarski(X14,k2_zfmisc_1(X15,X16)) )
      & ( r1_tarski(X14,k2_zfmisc_1(esk1_3(X14,X15,X16),esk2_3(X14,X15,X16)))
        | ~ v1_finset_1(X14)
        | ~ r1_tarski(X14,k2_zfmisc_1(X15,X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_finset_1])])])])).

fof(c_0_14,negated_conjecture,(
    ! [X22] :
      ( v1_finset_1(esk3_0)
      & r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))
      & ( ~ v1_finset_1(X22)
        | ~ r1_tarski(X22,esk4_0)
        | ~ r1_tarski(esk3_0,k2_zfmisc_1(X22,esk5_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X4))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,k2_zfmisc_1(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)))
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_tarski(esk3_0,k2_zfmisc_1(X1,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k2_zfmisc_1(esk1_3(X1,X2,X3),X4))
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(esk2_3(X1,X2,X3),X4)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( v1_finset_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_finset_1(esk1_3(esk3_0,X1,X2))
    | ~ r1_tarski(esk1_3(esk3_0,X1,X2),esk4_0)
    | ~ r1_tarski(esk2_3(esk3_0,X1,X2),esk5_0)
    | ~ r1_tarski(esk3_0,k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_21,plain,
    ( v1_finset_1(esk1_3(X1,X2,X3))
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_tarski(esk1_3(esk3_0,X1,X2),esk4_0)
    | ~ r1_tarski(esk2_3(esk3_0,X1,X2),esk5_0)
    | ~ r1_tarski(esk3_0,k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_19])])).

cnf(c_0_23,plain,
    ( r1_tarski(esk2_3(X1,X2,X3),X3)
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( ~ r1_tarski(esk1_3(esk3_0,X1,esk5_0),esk4_0)
    | ~ r1_tarski(esk3_0,k2_zfmisc_1(X1,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_19])])).

cnf(c_0_25,plain,
    ( r1_tarski(esk1_3(X1,X2,X3),X2)
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.16/0.36  % Computer   : n008.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 12:40:15 EST 2020
% 0.22/0.36  % CPUTime    : 
% 0.22/0.36  # Version: 2.5pre002
% 0.22/0.36  # No SInE strategy applied
% 0.22/0.36  # Trying AutoSched0 for 299 seconds
% 0.22/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.22/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.22/0.40  #
% 0.22/0.40  # Preprocessing time       : 0.027 s
% 0.22/0.40  # Presaturation interreduction done
% 0.22/0.40  
% 0.22/0.40  # Proof found!
% 0.22/0.40  # SZS status Theorem
% 0.22/0.40  # SZS output start CNFRefutation
% 0.22/0.40  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.22/0.40  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.22/0.40  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 0.22/0.40  fof(t33_finset_1, conjecture, ![X1, X2, X3]:~(((v1_finset_1(X1)&r1_tarski(X1,k2_zfmisc_1(X2,X3)))&![X4]:~(((v1_finset_1(X4)&r1_tarski(X4,X2))&r1_tarski(X1,k2_zfmisc_1(X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_finset_1)).
% 0.22/0.40  fof(t32_finset_1, axiom, ![X1, X2, X3]:~(((v1_finset_1(X1)&r1_tarski(X1,k2_zfmisc_1(X2,X3)))&![X4, X5]:~(((((v1_finset_1(X4)&r1_tarski(X4,X2))&v1_finset_1(X5))&r1_tarski(X5,X3))&r1_tarski(X1,k2_zfmisc_1(X4,X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_finset_1)).
% 0.22/0.40  fof(c_0_5, plain, ![X6, X7, X8]:(~r1_tarski(k2_xboole_0(X6,X7),X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.22/0.40  fof(c_0_6, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k2_xboole_0(X9,X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.22/0.40  cnf(c_0_7, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.22/0.40  cnf(c_0_8, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.22/0.40  fof(c_0_9, plain, ![X11, X12, X13]:((r1_tarski(k2_zfmisc_1(X11,X13),k2_zfmisc_1(X12,X13))|~r1_tarski(X11,X12))&(r1_tarski(k2_zfmisc_1(X13,X11),k2_zfmisc_1(X13,X12))|~r1_tarski(X11,X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 0.22/0.40  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:~(((v1_finset_1(X1)&r1_tarski(X1,k2_zfmisc_1(X2,X3)))&![X4]:~(((v1_finset_1(X4)&r1_tarski(X4,X2))&r1_tarski(X1,k2_zfmisc_1(X4,X3))))))), inference(assume_negation,[status(cth)],[t33_finset_1])).
% 0.22/0.40  cnf(c_0_11, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.22/0.40  cnf(c_0_12, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.22/0.40  fof(c_0_13, plain, ![X14, X15, X16]:(((((v1_finset_1(esk1_3(X14,X15,X16))|(~v1_finset_1(X14)|~r1_tarski(X14,k2_zfmisc_1(X15,X16))))&(r1_tarski(esk1_3(X14,X15,X16),X15)|(~v1_finset_1(X14)|~r1_tarski(X14,k2_zfmisc_1(X15,X16)))))&(v1_finset_1(esk2_3(X14,X15,X16))|(~v1_finset_1(X14)|~r1_tarski(X14,k2_zfmisc_1(X15,X16)))))&(r1_tarski(esk2_3(X14,X15,X16),X16)|(~v1_finset_1(X14)|~r1_tarski(X14,k2_zfmisc_1(X15,X16)))))&(r1_tarski(X14,k2_zfmisc_1(esk1_3(X14,X15,X16),esk2_3(X14,X15,X16)))|(~v1_finset_1(X14)|~r1_tarski(X14,k2_zfmisc_1(X15,X16))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_finset_1])])])])).
% 0.22/0.40  fof(c_0_14, negated_conjecture, ![X22]:((v1_finset_1(esk3_0)&r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0)))&(~v1_finset_1(X22)|~r1_tarski(X22,esk4_0)|~r1_tarski(esk3_0,k2_zfmisc_1(X22,esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.22/0.40  cnf(c_0_15, plain, (r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r1_tarski(X1,k2_zfmisc_1(X2,X4))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.22/0.40  cnf(c_0_16, plain, (r1_tarski(X1,k2_zfmisc_1(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)))|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.22/0.40  cnf(c_0_17, negated_conjecture, (~v1_finset_1(X1)|~r1_tarski(X1,esk4_0)|~r1_tarski(esk3_0,k2_zfmisc_1(X1,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.22/0.40  cnf(c_0_18, plain, (r1_tarski(X1,k2_zfmisc_1(esk1_3(X1,X2,X3),X4))|~v1_finset_1(X1)|~r1_tarski(esk2_3(X1,X2,X3),X4)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.22/0.40  cnf(c_0_19, negated_conjecture, (v1_finset_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.22/0.40  cnf(c_0_20, negated_conjecture, (~v1_finset_1(esk1_3(esk3_0,X1,X2))|~r1_tarski(esk1_3(esk3_0,X1,X2),esk4_0)|~r1_tarski(esk2_3(esk3_0,X1,X2),esk5_0)|~r1_tarski(esk3_0,k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.22/0.40  cnf(c_0_21, plain, (v1_finset_1(esk1_3(X1,X2,X3))|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.22/0.40  cnf(c_0_22, negated_conjecture, (~r1_tarski(esk1_3(esk3_0,X1,X2),esk4_0)|~r1_tarski(esk2_3(esk3_0,X1,X2),esk5_0)|~r1_tarski(esk3_0,k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_19])])).
% 0.22/0.40  cnf(c_0_23, plain, (r1_tarski(esk2_3(X1,X2,X3),X3)|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.22/0.40  cnf(c_0_24, negated_conjecture, (~r1_tarski(esk1_3(esk3_0,X1,esk5_0),esk4_0)|~r1_tarski(esk3_0,k2_zfmisc_1(X1,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_19])])).
% 0.22/0.40  cnf(c_0_25, plain, (r1_tarski(esk1_3(X1,X2,X3),X2)|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.22/0.40  cnf(c_0_26, negated_conjecture, (r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.22/0.40  cnf(c_0_27, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_19])]), ['proof']).
% 0.22/0.40  # SZS output end CNFRefutation
% 0.22/0.40  # Proof object total steps             : 28
% 0.22/0.40  # Proof object clause steps            : 17
% 0.22/0.40  # Proof object formula steps           : 11
% 0.22/0.40  # Proof object conjectures             : 10
% 0.22/0.40  # Proof object clause conjectures      : 7
% 0.22/0.40  # Proof object formula conjectures     : 3
% 0.22/0.40  # Proof object initial clauses used    : 10
% 0.22/0.40  # Proof object initial formulas used   : 5
% 0.22/0.40  # Proof object generating inferences   : 7
% 0.22/0.40  # Proof object simplifying inferences  : 9
% 0.22/0.40  # Training examples: 0 positive, 0 negative
% 0.22/0.40  # Parsed axioms                        : 5
% 0.22/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.40  # Initial clauses                      : 12
% 0.22/0.40  # Removed in clause preprocessing      : 0
% 0.22/0.40  # Initial clauses in saturation        : 12
% 0.22/0.40  # Processed clauses                    : 132
% 0.22/0.40  # ...of these trivial                  : 0
% 0.22/0.40  # ...subsumed                          : 27
% 0.22/0.40  # ...remaining for further processing  : 105
% 0.22/0.40  # Other redundant clauses eliminated   : 0
% 0.22/0.40  # Clauses deleted for lack of memory   : 0
% 0.22/0.40  # Backward-subsumed                    : 2
% 0.22/0.40  # Backward-rewritten                   : 0
% 0.22/0.40  # Generated clauses                    : 426
% 0.22/0.40  # ...of the previous two non-trivial   : 425
% 0.22/0.40  # Contextual simplify-reflections      : 1
% 0.22/0.40  # Paramodulations                      : 426
% 0.22/0.40  # Factorizations                       : 0
% 0.22/0.40  # Equation resolutions                 : 0
% 0.22/0.40  # Propositional unsat checks           : 0
% 0.22/0.40  #    Propositional check models        : 0
% 0.22/0.40  #    Propositional check unsatisfiable : 0
% 0.22/0.40  #    Propositional clauses             : 0
% 0.22/0.40  #    Propositional clauses after purity: 0
% 0.22/0.40  #    Propositional unsat core size     : 0
% 0.22/0.40  #    Propositional preprocessing time  : 0.000
% 0.22/0.40  #    Propositional encoding time       : 0.000
% 0.22/0.40  #    Propositional solver time         : 0.000
% 0.22/0.40  #    Success case prop preproc time    : 0.000
% 0.22/0.40  #    Success case prop encoding time   : 0.000
% 0.22/0.40  #    Success case prop solver time     : 0.000
% 0.22/0.40  # Current number of processed clauses  : 91
% 0.22/0.40  #    Positive orientable unit clauses  : 2
% 0.22/0.40  #    Positive unorientable unit clauses: 0
% 0.22/0.40  #    Negative unit clauses             : 0
% 0.22/0.40  #    Non-unit-clauses                  : 89
% 0.22/0.40  # Current number of unprocessed clauses: 317
% 0.22/0.40  # ...number of literals in the above   : 1455
% 0.22/0.40  # Current number of archived formulas  : 0
% 0.22/0.40  # Current number of archived clauses   : 14
% 0.22/0.40  # Clause-clause subsumption calls (NU) : 1566
% 0.22/0.40  # Rec. Clause-clause subsumption calls : 1152
% 0.22/0.40  # Non-unit clause-clause subsumptions  : 30
% 0.22/0.40  # Unit Clause-clause subsumption calls : 0
% 0.22/0.40  # Rewrite failures with RHS unbound    : 0
% 0.22/0.40  # BW rewrite match attempts            : 0
% 0.22/0.40  # BW rewrite match successes           : 0
% 0.22/0.40  # Condensation attempts                : 0
% 0.22/0.40  # Condensation successes               : 0
% 0.22/0.40  # Termbank termtop insertions          : 8282
% 0.22/0.40  
% 0.22/0.40  # -------------------------------------------------
% 0.22/0.40  # User time                : 0.039 s
% 0.22/0.40  # System time              : 0.005 s
% 0.22/0.40  # Total time               : 0.044 s
% 0.22/0.40  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
