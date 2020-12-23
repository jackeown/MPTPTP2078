%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:52 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   38 (  74 expanded)
%              Number of clauses        :   23 (  32 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :  106 ( 248 expanded)
%              Number of equality atoms :   16 (  38 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t56_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ! [X3] :
          ( m1_subset_1(X3,X1)
         => ( X1 != k1_xboole_0
           => m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t95_enumset1,axiom,(
    ! [X1,X2] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_enumset1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,X1)
       => ! [X3] :
            ( m1_subset_1(X3,X1)
           => ( X1 != k1_xboole_0
             => m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t56_subset_1])).

fof(c_0_8,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X22,X21)
        | r2_hidden(X22,X21)
        | v1_xboole_0(X21) )
      & ( ~ r2_hidden(X22,X21)
        | m1_subset_1(X22,X21)
        | v1_xboole_0(X21) )
      & ( ~ m1_subset_1(X22,X21)
        | v1_xboole_0(X22)
        | ~ v1_xboole_0(X21) )
      & ( ~ v1_xboole_0(X22)
        | m1_subset_1(X22,X21)
        | ~ v1_xboole_0(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_9,negated_conjecture,
    ( m1_subset_1(esk4_0,esk3_0)
    & m1_subset_1(esk5_0,esk3_0)
    & esk3_0 != k1_xboole_0
    & ~ m1_subset_1(k2_tarski(esk4_0,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X18,X19,X20] :
      ( ( r2_hidden(X18,X20)
        | ~ r1_tarski(k2_tarski(X18,X19),X20) )
      & ( r2_hidden(X19,X20)
        | ~ r1_tarski(k2_tarski(X18,X19),X20) )
      & ( ~ r2_hidden(X18,X20)
        | ~ r2_hidden(X19,X20)
        | r1_tarski(k2_tarski(X18,X19),X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_14,plain,(
    ! [X9,X10] : k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t95_enumset1])).

fof(c_0_15,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0)
    | v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

fof(c_0_23,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X13,X12)
        | r1_tarski(X13,X11)
        | X12 != k1_zfmisc_1(X11) )
      & ( ~ r1_tarski(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k1_zfmisc_1(X11) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | ~ r1_tarski(esk2_2(X15,X16),X15)
        | X16 = k1_zfmisc_1(X15) )
      & ( r2_hidden(esk2_2(X15,X16),X16)
        | r1_tarski(esk2_2(X15,X16),X15)
        | X16 = k1_zfmisc_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_24,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,esk5_0),esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_25]),c_0_26])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(esk4_0,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_30,c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( ~ m1_subset_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:22:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.14/0.38  # and selection function SelectNewComplexAHP.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t56_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_subset_1)).
% 0.14/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.14/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.14/0.38  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.14/0.38  fof(t95_enumset1, axiom, ![X1, X2]:k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_enumset1)).
% 0.14/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.14/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.14/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X1)))))), inference(assume_negation,[status(cth)],[t56_subset_1])).
% 0.14/0.38  fof(c_0_8, plain, ![X21, X22]:(((~m1_subset_1(X22,X21)|r2_hidden(X22,X21)|v1_xboole_0(X21))&(~r2_hidden(X22,X21)|m1_subset_1(X22,X21)|v1_xboole_0(X21)))&((~m1_subset_1(X22,X21)|v1_xboole_0(X22)|~v1_xboole_0(X21))&(~v1_xboole_0(X22)|m1_subset_1(X22,X21)|~v1_xboole_0(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.14/0.38  fof(c_0_9, negated_conjecture, (m1_subset_1(esk4_0,esk3_0)&(m1_subset_1(esk5_0,esk3_0)&(esk3_0!=k1_xboole_0&~m1_subset_1(k2_tarski(esk4_0,esk5_0),k1_zfmisc_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.14/0.38  fof(c_0_10, plain, ![X8]:(~v1_xboole_0(X8)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.14/0.38  cnf(c_0_11, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  fof(c_0_13, plain, ![X18, X19, X20]:(((r2_hidden(X18,X20)|~r1_tarski(k2_tarski(X18,X19),X20))&(r2_hidden(X19,X20)|~r1_tarski(k2_tarski(X18,X19),X20)))&(~r2_hidden(X18,X20)|~r2_hidden(X19,X20)|r1_tarski(k2_tarski(X18,X19),X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.14/0.38  fof(c_0_14, plain, ![X9, X10]:k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t95_enumset1])).
% 0.14/0.38  fof(c_0_15, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.14/0.38  cnf(c_0_16, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (r2_hidden(esk5_0,esk3_0)|v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_19, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_20, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_21, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.14/0.38  fof(c_0_23, plain, ![X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X13,X12)|r1_tarski(X13,X11)|X12!=k1_zfmisc_1(X11))&(~r1_tarski(X14,X11)|r2_hidden(X14,X12)|X12!=k1_zfmisc_1(X11)))&((~r2_hidden(esk2_2(X15,X16),X16)|~r1_tarski(esk2_2(X15,X16),X15)|X16=k1_zfmisc_1(X15))&(r2_hidden(esk2_2(X15,X16),X16)|r1_tarski(esk2_2(X15,X16),X15)|X16=k1_zfmisc_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.14/0.38  cnf(c_0_24, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.14/0.38  cnf(c_0_27, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,esk5_0),esk3_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_22])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_25]), c_0_26])).
% 0.14/0.38  cnf(c_0_30, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_31, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_27])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (r1_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (~m1_subset_1(k2_tarski(esk4_0,esk5_0),k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_34, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_30, c_0_21])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (~m1_subset_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[c_0_33, c_0_20])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 38
% 0.14/0.38  # Proof object clause steps            : 23
% 0.14/0.38  # Proof object formula steps           : 15
% 0.14/0.38  # Proof object conjectures             : 16
% 0.14/0.38  # Proof object clause conjectures      : 13
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 11
% 0.14/0.38  # Proof object initial formulas used   : 7
% 0.14/0.38  # Proof object generating inferences   : 9
% 0.14/0.38  # Proof object simplifying inferences  : 6
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 7
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 19
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 18
% 0.14/0.38  # Processed clauses                    : 81
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 20
% 0.14/0.38  # ...remaining for further processing  : 61
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 1
% 0.14/0.38  # Generated clauses                    : 181
% 0.14/0.38  # ...of the previous two non-trivial   : 145
% 0.14/0.38  # Contextual simplify-reflections      : 2
% 0.14/0.38  # Paramodulations                      : 173
% 0.14/0.38  # Factorizations                       : 6
% 0.14/0.38  # Equation resolutions                 : 2
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 60
% 0.14/0.38  #    Positive orientable unit clauses  : 15
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 4
% 0.14/0.38  #    Non-unit-clauses                  : 41
% 0.14/0.38  # Current number of unprocessed clauses: 78
% 0.14/0.38  # ...number of literals in the above   : 283
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 2
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 184
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 134
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 19
% 0.14/0.38  # Unit Clause-clause subsumption calls : 19
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 7
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 4669
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.028 s
% 0.14/0.38  # System time              : 0.007 s
% 0.14/0.38  # Total time               : 0.036 s
% 0.14/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
