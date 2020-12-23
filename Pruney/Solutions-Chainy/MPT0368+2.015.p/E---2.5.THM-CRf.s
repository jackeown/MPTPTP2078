%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:41 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  48 expanded)
%              Number of clauses        :   19 (  21 expanded)
%              Number of leaves         :    7 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 161 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( ! [X3] :
            ( m1_subset_1(X3,X1)
           => r2_hidden(X3,X2) )
       => X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t60_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_tarski(X1,X2)
        & r2_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( ! [X3] :
              ( m1_subset_1(X3,X1)
             => r2_hidden(X3,X2) )
         => X1 = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t49_subset_1])).

fof(c_0_8,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X19,X18)
        | r2_hidden(X19,X18)
        | v1_xboole_0(X18) )
      & ( ~ r2_hidden(X19,X18)
        | m1_subset_1(X19,X18)
        | v1_xboole_0(X18) )
      & ( ~ m1_subset_1(X19,X18)
        | v1_xboole_0(X19)
        | ~ v1_xboole_0(X18) )
      & ( ~ v1_xboole_0(X19)
        | m1_subset_1(X19,X18)
        | ~ v1_xboole_0(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_9,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_10,negated_conjecture,(
    ! [X25] :
      ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
      & ( ~ m1_subset_1(X25,esk3_0)
        | r2_hidden(X25,esk4_0) )
      & esk3_0 != esk4_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

cnf(c_0_11,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_16,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | ~ r2_hidden(X22,X21)
      | r2_hidden(X22,X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_17,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | ~ r2_xboole_0(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).

fof(c_0_18,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | ~ r2_xboole_0(X14,X15) )
      & ( X14 != X15
        | ~ r2_xboole_0(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | X14 = X15
        | r2_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r2_hidden(esk2_2(X1,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | r2_hidden(esk2_2(esk4_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_31]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:31:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t49_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(![X3]:(m1_subset_1(X3,X1)=>r2_hidden(X3,X2))=>X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 0.20/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.38  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.20/0.38  fof(t60_xboole_1, axiom, ![X1, X2]:~((r1_tarski(X1,X2)&r2_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 0.20/0.38  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.20/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(![X3]:(m1_subset_1(X3,X1)=>r2_hidden(X3,X2))=>X1=X2))), inference(assume_negation,[status(cth)],[t49_subset_1])).
% 0.20/0.38  fof(c_0_8, plain, ![X18, X19]:(((~m1_subset_1(X19,X18)|r2_hidden(X19,X18)|v1_xboole_0(X18))&(~r2_hidden(X19,X18)|m1_subset_1(X19,X18)|v1_xboole_0(X18)))&((~m1_subset_1(X19,X18)|v1_xboole_0(X19)|~v1_xboole_0(X18))&(~v1_xboole_0(X19)|m1_subset_1(X19,X18)|~v1_xboole_0(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.38  fof(c_0_9, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.38  fof(c_0_10, negated_conjecture, ![X25]:(m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&((~m1_subset_1(X25,esk3_0)|r2_hidden(X25,esk4_0))&esk3_0!=esk4_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.20/0.38  cnf(c_0_11, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_12, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  fof(c_0_13, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_14, negated_conjecture, (r2_hidden(X1,esk4_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_15, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.38  fof(c_0_16, plain, ![X20, X21, X22]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|(~r2_hidden(X22,X21)|r2_hidden(X22,X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.20/0.38  fof(c_0_17, plain, ![X16, X17]:(~r1_tarski(X16,X17)|~r2_xboole_0(X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).
% 0.20/0.38  fof(c_0_18, plain, ![X14, X15]:(((r1_tarski(X14,X15)|~r2_xboole_0(X14,X15))&(X14!=X15|~r2_xboole_0(X14,X15)))&(~r1_tarski(X14,X15)|X14=X15|r2_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.20/0.38  cnf(c_0_19, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.38  cnf(c_0_21, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_23, plain, (~r1_tarski(X1,X2)|~r2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_24, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (r1_tarski(X1,esk4_0)|~r2_hidden(esk2_2(X1,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.38  cnf(c_0_26, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.38  cnf(c_0_28, plain, (X1=X2|~r1_tarski(X2,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (r1_tarski(esk4_0,X1)|r2_hidden(esk2_2(esk4_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (~r1_tarski(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_31]), c_0_32]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 34
% 0.20/0.38  # Proof object clause steps            : 19
% 0.20/0.38  # Proof object formula steps           : 15
% 0.20/0.38  # Proof object conjectures             : 13
% 0.20/0.38  # Proof object clause conjectures      : 10
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 10
% 0.20/0.38  # Proof object initial formulas used   : 7
% 0.20/0.38  # Proof object generating inferences   : 8
% 0.20/0.38  # Proof object simplifying inferences  : 3
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 7
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 17
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 17
% 0.20/0.38  # Processed clauses                    : 47
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 7
% 0.20/0.38  # ...remaining for further processing  : 40
% 0.20/0.38  # Other redundant clauses eliminated   : 1
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 1
% 0.20/0.38  # Generated clauses                    : 42
% 0.20/0.38  # ...of the previous two non-trivial   : 33
% 0.20/0.38  # Contextual simplify-reflections      : 1
% 0.20/0.38  # Paramodulations                      : 40
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 1
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 37
% 0.20/0.38  #    Positive orientable unit clauses  : 5
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 6
% 0.20/0.38  #    Non-unit-clauses                  : 26
% 0.20/0.38  # Current number of unprocessed clauses: 2
% 0.20/0.38  # ...number of literals in the above   : 6
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 2
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 35
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 31
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 7
% 0.20/0.38  # Unit Clause-clause subsumption calls : 22
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 7
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 1410
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.027 s
% 0.20/0.38  # System time              : 0.005 s
% 0.20/0.38  # Total time               : 0.032 s
% 0.20/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
