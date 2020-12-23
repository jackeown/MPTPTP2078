%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:50 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 124 expanded)
%              Number of clauses        :   25 (  56 expanded)
%              Number of leaves         :    7 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 420 expanded)
%              Number of equality atoms :   23 (  85 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ( X1 != k1_xboole_0
       => m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t68_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(rc1_subset_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
          & ~ v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_subset_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,X1)
       => ( X1 != k1_xboole_0
         => m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t55_subset_1])).

fof(c_0_8,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X17,X16)
        | r2_hidden(X17,X16)
        | v1_xboole_0(X16) )
      & ( ~ r2_hidden(X17,X16)
        | m1_subset_1(X17,X16)
        | v1_xboole_0(X16) )
      & ( ~ m1_subset_1(X17,X16)
        | v1_xboole_0(X17)
        | ~ v1_xboole_0(X16) )
      & ( ~ v1_xboole_0(X17)
        | m1_subset_1(X17,X16)
        | ~ v1_xboole_0(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_9,negated_conjecture,
    ( m1_subset_1(esk4_0,esk3_0)
    & esk3_0 != k1_xboole_0
    & ~ m1_subset_1(k1_tarski(esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(k1_tarski(X14),X15) != k1_xboole_0
        | r2_hidden(X14,X15) )
      & ( ~ r2_hidden(X14,X15)
        | k4_xboole_0(k1_tarski(X14),X15) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_zfmisc_1])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X9,X8)
        | r1_tarski(X9,X7)
        | X8 != k1_zfmisc_1(X7) )
      & ( ~ r1_tarski(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k1_zfmisc_1(X7) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | ~ r1_tarski(esk1_2(X11,X12),X11)
        | X12 = k1_zfmisc_1(X11) )
      & ( r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(esk1_2(X11,X12),X11)
        | X12 = k1_zfmisc_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_14,plain,(
    ! [X5,X6] :
      ( ( k4_xboole_0(X5,X6) != k1_xboole_0
        | r1_tarski(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | k4_xboole_0(X5,X6) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_15,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk4_0),esk3_0) = k1_xboole_0
    | v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k1_tarski(esk4_0),esk3_0)
    | v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_22,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k1_tarski(esk4_0),k1_zfmisc_1(esk3_0))
    | v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( ~ m1_subset_1(k1_tarski(esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk3_0))
    | v1_xboole_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( k1_zfmisc_1(esk3_0) = k1_xboole_0
    | v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_29,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_30,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_31,plain,(
    ! [X18] :
      ( ( m1_subset_1(esk2_1(X18),k1_zfmisc_1(X18))
        | v1_xboole_0(X18) )
      & ( ~ v1_xboole_0(esk2_1(X18))
        | v1_xboole_0(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc1_subset_1])])])])])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_29]),c_0_30])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk2_1(esk3_0),k1_xboole_0)
    | v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_28])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_38]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n014.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 14:41:37 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.12/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.12/0.35  # and selection function SelectSmallestOrientable.
% 0.12/0.35  #
% 0.12/0.35  # Preprocessing time       : 0.027 s
% 0.12/0.35  # Presaturation interreduction done
% 0.12/0.35  
% 0.12/0.35  # Proof found!
% 0.12/0.35  # SZS status Theorem
% 0.12/0.35  # SZS output start CNFRefutation
% 0.12/0.35  fof(t55_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 0.12/0.35  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.12/0.35  fof(t68_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 0.12/0.35  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.12/0.35  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.12/0.35  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.12/0.35  fof(rc1_subset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_subset_1)).
% 0.12/0.35  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1))))), inference(assume_negation,[status(cth)],[t55_subset_1])).
% 0.12/0.35  fof(c_0_8, plain, ![X16, X17]:(((~m1_subset_1(X17,X16)|r2_hidden(X17,X16)|v1_xboole_0(X16))&(~r2_hidden(X17,X16)|m1_subset_1(X17,X16)|v1_xboole_0(X16)))&((~m1_subset_1(X17,X16)|v1_xboole_0(X17)|~v1_xboole_0(X16))&(~v1_xboole_0(X17)|m1_subset_1(X17,X16)|~v1_xboole_0(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.12/0.35  fof(c_0_9, negated_conjecture, (m1_subset_1(esk4_0,esk3_0)&(esk3_0!=k1_xboole_0&~m1_subset_1(k1_tarski(esk4_0),k1_zfmisc_1(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.12/0.35  fof(c_0_10, plain, ![X14, X15]:((k4_xboole_0(k1_tarski(X14),X15)!=k1_xboole_0|r2_hidden(X14,X15))&(~r2_hidden(X14,X15)|k4_xboole_0(k1_tarski(X14),X15)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_zfmisc_1])])).
% 0.12/0.35  cnf(c_0_11, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.35  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.35  fof(c_0_13, plain, ![X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X9,X8)|r1_tarski(X9,X7)|X8!=k1_zfmisc_1(X7))&(~r1_tarski(X10,X7)|r2_hidden(X10,X8)|X8!=k1_zfmisc_1(X7)))&((~r2_hidden(esk1_2(X11,X12),X12)|~r1_tarski(esk1_2(X11,X12),X11)|X12=k1_zfmisc_1(X11))&(r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(esk1_2(X11,X12),X11)|X12=k1_zfmisc_1(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.12/0.35  fof(c_0_14, plain, ![X5, X6]:((k4_xboole_0(X5,X6)!=k1_xboole_0|r1_tarski(X5,X6))&(~r1_tarski(X5,X6)|k4_xboole_0(X5,X6)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.12/0.35  cnf(c_0_15, plain, (k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  cnf(c_0_16, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.12/0.35  cnf(c_0_17, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.35  cnf(c_0_18, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.35  cnf(c_0_19, negated_conjecture, (k4_xboole_0(k1_tarski(esk4_0),esk3_0)=k1_xboole_0|v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.35  cnf(c_0_20, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_17])).
% 0.12/0.35  cnf(c_0_21, negated_conjecture, (r1_tarski(k1_tarski(esk4_0),esk3_0)|v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.35  fof(c_0_22, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.12/0.35  cnf(c_0_23, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.35  cnf(c_0_24, negated_conjecture, (r2_hidden(k1_tarski(esk4_0),k1_zfmisc_1(esk3_0))|v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.35  cnf(c_0_25, negated_conjecture, (~m1_subset_1(k1_tarski(esk4_0),k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.35  cnf(c_0_26, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.35  cnf(c_0_27, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(esk3_0))|v1_xboole_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.12/0.35  cnf(c_0_28, negated_conjecture, (k1_zfmisc_1(esk3_0)=k1_xboole_0|v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.35  cnf(c_0_29, negated_conjecture, (v1_xboole_0(esk3_0)|v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.35  cnf(c_0_30, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.35  fof(c_0_31, plain, ![X18]:((m1_subset_1(esk2_1(X18),k1_zfmisc_1(X18))|v1_xboole_0(X18))&(~v1_xboole_0(esk2_1(X18))|v1_xboole_0(X18))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc1_subset_1])])])])])).
% 0.12/0.35  cnf(c_0_32, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.35  cnf(c_0_33, negated_conjecture, (v1_xboole_0(k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_29]), c_0_30])).
% 0.12/0.35  cnf(c_0_34, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1))|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.35  cnf(c_0_35, negated_conjecture, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.35  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk2_1(esk3_0),k1_xboole_0)|v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_28])).
% 0.12/0.35  cnf(c_0_37, plain, (v1_xboole_0(X1)|~v1_xboole_0(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.35  cnf(c_0_38, negated_conjecture, (v1_xboole_0(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.12/0.35  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_38]), c_0_30]), ['proof']).
% 0.12/0.35  # SZS output end CNFRefutation
% 0.12/0.35  # Proof object total steps             : 40
% 0.12/0.35  # Proof object clause steps            : 25
% 0.12/0.35  # Proof object formula steps           : 15
% 0.12/0.35  # Proof object conjectures             : 18
% 0.12/0.35  # Proof object clause conjectures      : 15
% 0.12/0.35  # Proof object formula conjectures     : 3
% 0.12/0.35  # Proof object initial clauses used    : 12
% 0.12/0.35  # Proof object initial formulas used   : 7
% 0.12/0.35  # Proof object generating inferences   : 12
% 0.12/0.35  # Proof object simplifying inferences  : 5
% 0.12/0.35  # Training examples: 0 positive, 0 negative
% 0.12/0.35  # Parsed axioms                        : 7
% 0.12/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.35  # Initial clauses                      : 18
% 0.12/0.35  # Removed in clause preprocessing      : 0
% 0.12/0.35  # Initial clauses in saturation        : 18
% 0.12/0.35  # Processed clauses                    : 65
% 0.12/0.35  # ...of these trivial                  : 0
% 0.12/0.35  # ...subsumed                          : 5
% 0.12/0.35  # ...remaining for further processing  : 60
% 0.12/0.35  # Other redundant clauses eliminated   : 2
% 0.12/0.35  # Clauses deleted for lack of memory   : 0
% 0.12/0.35  # Backward-subsumed                    : 0
% 0.12/0.35  # Backward-rewritten                   : 12
% 0.12/0.35  # Generated clauses                    : 95
% 0.12/0.35  # ...of the previous two non-trivial   : 84
% 0.12/0.35  # Contextual simplify-reflections      : 1
% 0.12/0.35  # Paramodulations                      : 93
% 0.12/0.35  # Factorizations                       : 0
% 0.12/0.35  # Equation resolutions                 : 2
% 0.12/0.35  # Propositional unsat checks           : 0
% 0.12/0.35  #    Propositional check models        : 0
% 0.12/0.35  #    Propositional check unsatisfiable : 0
% 0.12/0.35  #    Propositional clauses             : 0
% 0.12/0.35  #    Propositional clauses after purity: 0
% 0.12/0.35  #    Propositional unsat core size     : 0
% 0.12/0.35  #    Propositional preprocessing time  : 0.000
% 0.12/0.35  #    Propositional encoding time       : 0.000
% 0.12/0.35  #    Propositional solver time         : 0.000
% 0.12/0.35  #    Success case prop preproc time    : 0.000
% 0.12/0.35  #    Success case prop encoding time   : 0.000
% 0.12/0.35  #    Success case prop solver time     : 0.000
% 0.12/0.35  # Current number of processed clauses  : 28
% 0.12/0.35  #    Positive orientable unit clauses  : 4
% 0.12/0.35  #    Positive unorientable unit clauses: 0
% 0.12/0.35  #    Negative unit clauses             : 2
% 0.12/0.35  #    Non-unit-clauses                  : 22
% 0.12/0.35  # Current number of unprocessed clauses: 53
% 0.12/0.35  # ...number of literals in the above   : 218
% 0.12/0.35  # Current number of archived formulas  : 0
% 0.12/0.35  # Current number of archived clauses   : 30
% 0.12/0.35  # Clause-clause subsumption calls (NU) : 177
% 0.12/0.35  # Rec. Clause-clause subsumption calls : 143
% 0.12/0.35  # Non-unit clause-clause subsumptions  : 6
% 0.12/0.35  # Unit Clause-clause subsumption calls : 18
% 0.12/0.35  # Rewrite failures with RHS unbound    : 0
% 0.12/0.35  # BW rewrite match attempts            : 2
% 0.12/0.35  # BW rewrite match successes           : 2
% 0.12/0.35  # Condensation attempts                : 0
% 0.12/0.35  # Condensation successes               : 0
% 0.12/0.35  # Termbank termtop insertions          : 2293
% 0.12/0.35  
% 0.12/0.35  # -------------------------------------------------
% 0.12/0.35  # User time                : 0.028 s
% 0.12/0.35  # System time              : 0.005 s
% 0.12/0.35  # Total time               : 0.033 s
% 0.12/0.35  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
