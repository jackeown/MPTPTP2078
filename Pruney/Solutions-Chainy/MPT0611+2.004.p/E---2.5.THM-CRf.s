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
% DateTime   : Thu Dec  3 10:52:39 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  76 expanded)
%              Number of clauses        :   26 (  34 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :   15
%              Number of atoms          :   99 ( 272 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t215_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
           => r1_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t215_relat_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
             => r1_xboole_0(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t215_relat_1])).

fof(c_0_7,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_xboole_0(X13,X14) )
      & ( r2_hidden(esk2_2(X13,X14),X14)
        | r1_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & r1_xboole_0(k2_relat_1(esk3_0),k2_relat_1(esk4_0))
    & ~ r1_xboole_0(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk3_0),k2_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X11,X12] :
      ( ~ r1_xboole_0(X11,X12)
      | r1_xboole_0(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_12,plain,(
    ! [X19,X20,X21,X22] :
      ( ( ~ r1_xboole_0(X19,X20)
        | r1_xboole_0(k2_zfmisc_1(X19,X21),k2_zfmisc_1(X20,X22)) )
      & ( ~ r1_xboole_0(X21,X22)
        | r1_xboole_0(k2_zfmisc_1(X19,X21),k2_zfmisc_1(X20,X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

cnf(c_0_13,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk4_0))
    | ~ r2_hidden(X1,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r1_xboole_0(X1,k2_relat_1(esk3_0))
    | ~ r2_hidden(esk2_2(X1,k2_relat_1(esk3_0)),k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r1_xboole_0(X4,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk4_0),k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(X1,k2_relat_1(esk3_0)),k2_zfmisc_1(X2,k2_relat_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_22,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k2_relat_1(esk4_0)))
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,k2_relat_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_21])).

cnf(c_0_24,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( r1_xboole_0(X1,k2_zfmisc_1(X2,k2_relat_1(esk4_0)))
    | ~ r2_hidden(esk2_2(X1,k2_zfmisc_1(X2,k2_relat_1(esk4_0))),k2_zfmisc_1(X3,k2_relat_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_14])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

fof(c_0_27,plain,(
    ! [X23] :
      ( ~ v1_relat_1(X23)
      | r1_tarski(X23,k2_zfmisc_1(k1_relat_1(X23),k2_relat_1(X23))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

cnf(c_0_28,negated_conjecture,
    ( r1_xboole_0(X1,k2_zfmisc_1(X2,k2_relat_1(esk4_0)))
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,k2_relat_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_zfmisc_1(X1,k2_relat_1(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k2_relat_1(esk4_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_31])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),esk3_0)
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,k2_relat_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,negated_conjecture,
    ( r1_xboole_0(X1,esk4_0)
    | ~ r2_hidden(esk2_2(X1,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_29]),c_0_35])])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_18]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:00:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S033N
% 0.19/0.38  # and selection function PSelectUnlessUniqMax.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.039 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t215_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2))=>r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t215_relat_1)).
% 0.19/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.38  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.38  fof(t127_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 0.19/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.38  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 0.19/0.38  fof(c_0_6, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2))=>r1_xboole_0(X1,X2))))), inference(assume_negation,[status(cth)],[t215_relat_1])).
% 0.19/0.38  fof(c_0_7, plain, ![X13, X14, X16, X17, X18]:(((r2_hidden(esk2_2(X13,X14),X13)|r1_xboole_0(X13,X14))&(r2_hidden(esk2_2(X13,X14),X14)|r1_xboole_0(X13,X14)))&(~r2_hidden(X18,X16)|~r2_hidden(X18,X17)|~r1_xboole_0(X16,X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.38  fof(c_0_8, negated_conjecture, (v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&(r1_xboole_0(k2_relat_1(esk3_0),k2_relat_1(esk4_0))&~r1_xboole_0(esk3_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.19/0.38  cnf(c_0_9, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_10, negated_conjecture, (r1_xboole_0(k2_relat_1(esk3_0),k2_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  fof(c_0_11, plain, ![X11, X12]:(~r1_xboole_0(X11,X12)|r1_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.38  fof(c_0_12, plain, ![X19, X20, X21, X22]:((~r1_xboole_0(X19,X20)|r1_xboole_0(k2_zfmisc_1(X19,X21),k2_zfmisc_1(X20,X22)))&(~r1_xboole_0(X21,X22)|r1_xboole_0(k2_zfmisc_1(X19,X21),k2_zfmisc_1(X20,X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).
% 0.19/0.38  cnf(c_0_13, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk4_0))|~r2_hidden(X1,k2_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.19/0.38  cnf(c_0_14, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_15, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_16, plain, (r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (r1_xboole_0(X1,k2_relat_1(esk3_0))|~r2_hidden(esk2_2(X1,k2_relat_1(esk3_0)),k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.38  cnf(c_0_18, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_19, plain, (r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))|~r1_xboole_0(X4,X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (r1_xboole_0(k2_relat_1(esk4_0),k2_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(X1,k2_relat_1(esk3_0)),k2_zfmisc_1(X2,k2_relat_1(esk4_0)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.38  fof(c_0_22, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (~r2_hidden(X1,k2_zfmisc_1(X2,k2_relat_1(esk4_0)))|~r2_hidden(X1,k2_zfmisc_1(X3,k2_relat_1(esk3_0)))), inference(spm,[status(thm)],[c_0_9, c_0_21])).
% 0.19/0.38  cnf(c_0_24, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (r1_xboole_0(X1,k2_zfmisc_1(X2,k2_relat_1(esk4_0)))|~r2_hidden(esk2_2(X1,k2_zfmisc_1(X2,k2_relat_1(esk4_0))),k2_zfmisc_1(X3,k2_relat_1(esk3_0)))), inference(spm,[status(thm)],[c_0_23, c_0_14])).
% 0.19/0.38  cnf(c_0_26, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_24, c_0_18])).
% 0.19/0.38  fof(c_0_27, plain, ![X23]:(~v1_relat_1(X23)|r1_tarski(X23,k2_zfmisc_1(k1_relat_1(X23),k2_relat_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (r1_xboole_0(X1,k2_zfmisc_1(X2,k2_relat_1(esk4_0)))|~r1_tarski(X1,k2_zfmisc_1(X3,k2_relat_1(esk3_0)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.38  cnf(c_0_29, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (r1_xboole_0(esk3_0,k2_zfmisc_1(X1,k2_relat_1(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (~r2_hidden(X1,k2_zfmisc_1(X2,k2_relat_1(esk4_0)))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_9, c_0_31])).
% 0.19/0.38  cnf(c_0_33, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_24, c_0_14])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (r1_xboole_0(X1,X2)|~r2_hidden(esk2_2(X1,X2),esk3_0)|~r1_tarski(X2,k2_zfmisc_1(X3,k2_relat_1(esk4_0)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (r1_xboole_0(X1,esk4_0)|~r2_hidden(esk2_2(X1,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_29]), c_0_35])])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (~r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_18]), c_0_37]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 39
% 0.19/0.38  # Proof object clause steps            : 26
% 0.19/0.38  # Proof object formula steps           : 13
% 0.19/0.38  # Proof object conjectures             : 19
% 0.19/0.38  # Proof object clause conjectures      : 16
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 11
% 0.19/0.38  # Proof object initial formulas used   : 6
% 0.19/0.38  # Proof object generating inferences   : 15
% 0.19/0.38  # Proof object simplifying inferences  : 5
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 6
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 14
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 14
% 0.19/0.38  # Processed clauses                    : 123
% 0.19/0.38  # ...of these trivial                  : 9
% 0.19/0.38  # ...subsumed                          : 13
% 0.19/0.38  # ...remaining for further processing  : 101
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 254
% 0.19/0.38  # ...of the previous two non-trivial   : 222
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 254
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
% 0.19/0.38  # Current number of processed clauses  : 87
% 0.19/0.38  #    Positive orientable unit clauses  : 23
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 63
% 0.19/0.38  # Current number of unprocessed clauses: 127
% 0.19/0.38  # ...number of literals in the above   : 238
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 14
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 443
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 303
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 13
% 0.19/0.38  # Unit Clause-clause subsumption calls : 3
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 19
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 4858
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.044 s
% 0.19/0.39  # System time              : 0.005 s
% 0.19/0.39  # Total time               : 0.050 s
% 0.19/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
