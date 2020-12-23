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
% DateTime   : Thu Dec  3 11:08:31 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  52 expanded)
%              Number of clauses        :   15 (  19 expanded)
%              Number of leaves         :    4 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 249 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_finset_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( v1_finset_1(X1)
        & r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & ! [X4] :
            ~ ( v1_finset_1(X4)
              & r1_tarski(X4,X2)
              & r1_tarski(X1,k2_zfmisc_1(X4,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_finset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_finset_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( v1_finset_1(X1)
          & r1_tarski(X1,k2_zfmisc_1(X2,X3))
          & ! [X4] :
              ~ ( v1_finset_1(X4)
                & r1_tarski(X4,X2)
                & r1_tarski(X1,k2_zfmisc_1(X4,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t33_finset_1])).

fof(c_0_5,negated_conjecture,(
    ! [X20] :
      ( v1_finset_1(esk3_0)
      & r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))
      & ( ~ v1_finset_1(X20)
        | ~ r1_tarski(X20,esk4_0)
        | ~ r1_tarski(esk3_0,k2_zfmisc_1(X20,esk5_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_6,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_7,negated_conjecture,
    ( ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_tarski(esk3_0,k2_zfmisc_1(X1,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X9,X10,X11] :
      ( ( r1_tarski(k2_zfmisc_1(X9,X11),k2_zfmisc_1(X10,X11))
        | ~ r1_tarski(X9,X10) )
      & ( r1_tarski(k2_zfmisc_1(X11,X9),k2_zfmisc_1(X11,X10))
        | ~ r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

cnf(c_0_10,negated_conjecture,
    ( ~ v1_finset_1(X1)
    | ~ r1_tarski(X2,k2_zfmisc_1(X1,esk5_0))
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_tarski(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X12,X13,X14] :
      ( ( v1_finset_1(esk1_3(X12,X13,X14))
        | ~ v1_finset_1(X12)
        | ~ r1_tarski(X12,k2_zfmisc_1(X13,X14)) )
      & ( r1_tarski(esk1_3(X12,X13,X14),X13)
        | ~ v1_finset_1(X12)
        | ~ r1_tarski(X12,k2_zfmisc_1(X13,X14)) )
      & ( v1_finset_1(esk2_3(X12,X13,X14))
        | ~ v1_finset_1(X12)
        | ~ r1_tarski(X12,k2_zfmisc_1(X13,X14)) )
      & ( r1_tarski(esk2_3(X12,X13,X14),X14)
        | ~ v1_finset_1(X12)
        | ~ r1_tarski(X12,k2_zfmisc_1(X13,X14)) )
      & ( r1_tarski(X12,k2_zfmisc_1(esk1_3(X12,X13,X14),esk2_3(X12,X13,X14)))
        | ~ v1_finset_1(X12)
        | ~ r1_tarski(X12,k2_zfmisc_1(X13,X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_finset_1])])])])).

cnf(c_0_13,negated_conjecture,
    ( ~ v1_finset_1(X1)
    | ~ r1_tarski(esk3_0,k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X2,esk5_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,k2_zfmisc_1(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)))
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( v1_finset_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( ~ v1_finset_1(esk1_3(esk3_0,X1,X2))
    | ~ r1_tarski(esk1_3(esk3_0,X1,X2),esk4_0)
    | ~ r1_tarski(esk2_3(esk3_0,X1,X2),esk5_0)
    | ~ r1_tarski(esk3_0,k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_17,plain,
    ( r1_tarski(esk1_3(X1,X2,X3),X2)
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( ~ v1_finset_1(esk1_3(esk3_0,esk4_0,X1))
    | ~ r1_tarski(esk2_3(esk3_0,esk4_0,X1),esk5_0)
    | ~ r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_15])])).

cnf(c_0_19,plain,
    ( r1_tarski(esk2_3(X1,X2,X3),X3)
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( ~ v1_finset_1(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_15])])).

cnf(c_0_22,plain,
    ( v1_finset_1(esk1_3(X1,X2,X3))
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_15]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:47:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S022N
% 0.20/0.50  # and selection function SelectOptimalRestrDepth2.
% 0.20/0.50  #
% 0.20/0.50  # Preprocessing time       : 0.045 s
% 0.20/0.50  # Presaturation interreduction done
% 0.20/0.50  
% 0.20/0.50  # Proof found!
% 0.20/0.50  # SZS status Theorem
% 0.20/0.50  # SZS output start CNFRefutation
% 0.20/0.50  fof(t33_finset_1, conjecture, ![X1, X2, X3]:~(((v1_finset_1(X1)&r1_tarski(X1,k2_zfmisc_1(X2,X3)))&![X4]:~(((v1_finset_1(X4)&r1_tarski(X4,X2))&r1_tarski(X1,k2_zfmisc_1(X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_finset_1)).
% 0.20/0.50  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.50  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 0.20/0.50  fof(t32_finset_1, axiom, ![X1, X2, X3]:~(((v1_finset_1(X1)&r1_tarski(X1,k2_zfmisc_1(X2,X3)))&![X4, X5]:~(((((v1_finset_1(X4)&r1_tarski(X4,X2))&v1_finset_1(X5))&r1_tarski(X5,X3))&r1_tarski(X1,k2_zfmisc_1(X4,X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_finset_1)).
% 0.20/0.50  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:~(((v1_finset_1(X1)&r1_tarski(X1,k2_zfmisc_1(X2,X3)))&![X4]:~(((v1_finset_1(X4)&r1_tarski(X4,X2))&r1_tarski(X1,k2_zfmisc_1(X4,X3))))))), inference(assume_negation,[status(cth)],[t33_finset_1])).
% 0.20/0.50  fof(c_0_5, negated_conjecture, ![X20]:((v1_finset_1(esk3_0)&r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0)))&(~v1_finset_1(X20)|~r1_tarski(X20,esk4_0)|~r1_tarski(esk3_0,k2_zfmisc_1(X20,esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.20/0.50  fof(c_0_6, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.50  cnf(c_0_7, negated_conjecture, (~v1_finset_1(X1)|~r1_tarski(X1,esk4_0)|~r1_tarski(esk3_0,k2_zfmisc_1(X1,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.50  cnf(c_0_8, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.50  fof(c_0_9, plain, ![X9, X10, X11]:((r1_tarski(k2_zfmisc_1(X9,X11),k2_zfmisc_1(X10,X11))|~r1_tarski(X9,X10))&(r1_tarski(k2_zfmisc_1(X11,X9),k2_zfmisc_1(X11,X10))|~r1_tarski(X9,X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 0.20/0.50  cnf(c_0_10, negated_conjecture, (~v1_finset_1(X1)|~r1_tarski(X2,k2_zfmisc_1(X1,esk5_0))|~r1_tarski(X1,esk4_0)|~r1_tarski(esk3_0,X2)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.20/0.50  cnf(c_0_11, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.50  fof(c_0_12, plain, ![X12, X13, X14]:(((((v1_finset_1(esk1_3(X12,X13,X14))|(~v1_finset_1(X12)|~r1_tarski(X12,k2_zfmisc_1(X13,X14))))&(r1_tarski(esk1_3(X12,X13,X14),X13)|(~v1_finset_1(X12)|~r1_tarski(X12,k2_zfmisc_1(X13,X14)))))&(v1_finset_1(esk2_3(X12,X13,X14))|(~v1_finset_1(X12)|~r1_tarski(X12,k2_zfmisc_1(X13,X14)))))&(r1_tarski(esk2_3(X12,X13,X14),X14)|(~v1_finset_1(X12)|~r1_tarski(X12,k2_zfmisc_1(X13,X14)))))&(r1_tarski(X12,k2_zfmisc_1(esk1_3(X12,X13,X14),esk2_3(X12,X13,X14)))|(~v1_finset_1(X12)|~r1_tarski(X12,k2_zfmisc_1(X13,X14))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_finset_1])])])])).
% 0.20/0.50  cnf(c_0_13, negated_conjecture, (~v1_finset_1(X1)|~r1_tarski(esk3_0,k2_zfmisc_1(X1,X2))|~r1_tarski(X1,esk4_0)|~r1_tarski(X2,esk5_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.50  cnf(c_0_14, plain, (r1_tarski(X1,k2_zfmisc_1(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)))|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.50  cnf(c_0_15, negated_conjecture, (v1_finset_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.50  cnf(c_0_16, negated_conjecture, (~v1_finset_1(esk1_3(esk3_0,X1,X2))|~r1_tarski(esk1_3(esk3_0,X1,X2),esk4_0)|~r1_tarski(esk2_3(esk3_0,X1,X2),esk5_0)|~r1_tarski(esk3_0,k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.20/0.50  cnf(c_0_17, plain, (r1_tarski(esk1_3(X1,X2,X3),X2)|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.50  cnf(c_0_18, negated_conjecture, (~v1_finset_1(esk1_3(esk3_0,esk4_0,X1))|~r1_tarski(esk2_3(esk3_0,esk4_0,X1),esk5_0)|~r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_15])])).
% 0.20/0.50  cnf(c_0_19, plain, (r1_tarski(esk2_3(X1,X2,X3),X3)|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.50  cnf(c_0_20, negated_conjecture, (r1_tarski(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.50  cnf(c_0_21, negated_conjecture, (~v1_finset_1(esk1_3(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_15])])).
% 0.20/0.50  cnf(c_0_22, plain, (v1_finset_1(esk1_3(X1,X2,X3))|~v1_finset_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.50  cnf(c_0_23, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_15]), c_0_20])]), ['proof']).
% 0.20/0.50  # SZS output end CNFRefutation
% 0.20/0.50  # Proof object total steps             : 24
% 0.20/0.50  # Proof object clause steps            : 15
% 0.20/0.50  # Proof object formula steps           : 9
% 0.20/0.50  # Proof object conjectures             : 12
% 0.20/0.50  # Proof object clause conjectures      : 9
% 0.20/0.50  # Proof object formula conjectures     : 3
% 0.20/0.50  # Proof object initial clauses used    : 9
% 0.20/0.50  # Proof object initial formulas used   : 4
% 0.20/0.50  # Proof object generating inferences   : 6
% 0.20/0.50  # Proof object simplifying inferences  : 10
% 0.20/0.50  # Training examples: 0 positive, 0 negative
% 0.20/0.50  # Parsed axioms                        : 4
% 0.20/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.50  # Initial clauses                      : 11
% 0.20/0.50  # Removed in clause preprocessing      : 0
% 0.20/0.50  # Initial clauses in saturation        : 11
% 0.20/0.50  # Processed clauses                    : 636
% 0.20/0.50  # ...of these trivial                  : 0
% 0.20/0.50  # ...subsumed                          : 453
% 0.20/0.50  # ...remaining for further processing  : 183
% 0.20/0.50  # Other redundant clauses eliminated   : 0
% 0.20/0.50  # Clauses deleted for lack of memory   : 0
% 0.20/0.50  # Backward-subsumed                    : 16
% 0.20/0.50  # Backward-rewritten                   : 0
% 0.20/0.50  # Generated clauses                    : 4991
% 0.20/0.50  # ...of the previous two non-trivial   : 4990
% 0.20/0.50  # Contextual simplify-reflections      : 1
% 0.20/0.50  # Paramodulations                      : 4991
% 0.20/0.50  # Factorizations                       : 0
% 0.20/0.50  # Equation resolutions                 : 0
% 0.20/0.50  # Propositional unsat checks           : 0
% 0.20/0.50  #    Propositional check models        : 0
% 0.20/0.50  #    Propositional check unsatisfiable : 0
% 0.20/0.50  #    Propositional clauses             : 0
% 0.20/0.50  #    Propositional clauses after purity: 0
% 0.20/0.50  #    Propositional unsat core size     : 0
% 0.20/0.50  #    Propositional preprocessing time  : 0.000
% 0.20/0.50  #    Propositional encoding time       : 0.000
% 0.20/0.50  #    Propositional solver time         : 0.000
% 0.20/0.50  #    Success case prop preproc time    : 0.000
% 0.20/0.50  #    Success case prop encoding time   : 0.000
% 0.20/0.50  #    Success case prop solver time     : 0.000
% 0.20/0.50  # Current number of processed clauses  : 156
% 0.20/0.50  #    Positive orientable unit clauses  : 2
% 0.20/0.50  #    Positive unorientable unit clauses: 0
% 0.20/0.50  #    Negative unit clauses             : 1
% 0.20/0.50  #    Non-unit-clauses                  : 153
% 0.20/0.50  # Current number of unprocessed clauses: 4348
% 0.20/0.50  # ...number of literals in the above   : 26530
% 0.20/0.50  # Current number of archived formulas  : 0
% 0.20/0.50  # Current number of archived clauses   : 27
% 0.20/0.50  # Clause-clause subsumption calls (NU) : 16136
% 0.20/0.50  # Rec. Clause-clause subsumption calls : 4148
% 0.20/0.50  # Non-unit clause-clause subsumptions  : 470
% 0.20/0.50  # Unit Clause-clause subsumption calls : 66
% 0.20/0.50  # Rewrite failures with RHS unbound    : 0
% 0.20/0.50  # BW rewrite match attempts            : 0
% 0.20/0.50  # BW rewrite match successes           : 0
% 0.20/0.50  # Condensation attempts                : 0
% 0.20/0.50  # Condensation successes               : 0
% 0.20/0.50  # Termbank termtop insertions          : 95250
% 0.20/0.50  
% 0.20/0.50  # -------------------------------------------------
% 0.20/0.50  # User time                : 0.156 s
% 0.20/0.50  # System time              : 0.009 s
% 0.20/0.50  # Total time               : 0.165 s
% 0.20/0.50  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
