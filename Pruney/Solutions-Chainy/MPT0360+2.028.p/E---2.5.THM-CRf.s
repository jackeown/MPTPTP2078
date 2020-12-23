%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:12 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   50 (  93 expanded)
%              Number of clauses        :   31 (  43 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  147 ( 332 expanded)
%              Number of equality atoms :   20 (  52 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_subset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X2,k3_subset_1(X1,X3)) )
       => X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

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

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t35_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,k3_subset_1(X1,X3))
           => r1_tarski(X3,k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(t38_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X1))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X2,k3_subset_1(X1,X3)) )
         => X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t40_subset_1])).

fof(c_0_10,plain,(
    ! [X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X14,X13)
        | r1_tarski(X14,X12)
        | X13 != k1_zfmisc_1(X12) )
      & ( ~ r1_tarski(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k1_zfmisc_1(X12) )
      & ( ~ r2_hidden(esk2_2(X16,X17),X17)
        | ~ r1_tarski(esk2_2(X16,X17),X16)
        | X17 = k1_zfmisc_1(X16) )
      & ( r2_hidden(esk2_2(X16,X17),X17)
        | r1_tarski(esk2_2(X16,X17),X16)
        | X17 = k1_zfmisc_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_11,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X20,X19)
        | r2_hidden(X20,X19)
        | v1_xboole_0(X19) )
      & ( ~ r2_hidden(X20,X19)
        | m1_subset_1(X20,X19)
        | v1_xboole_0(X19) )
      & ( ~ m1_subset_1(X20,X19)
        | v1_xboole_0(X20)
        | ~ v1_xboole_0(X19) )
      & ( ~ v1_xboole_0(X20)
        | m1_subset_1(X20,X19)
        | ~ v1_xboole_0(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_12,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
    & r1_tarski(esk4_0,esk5_0)
    & r1_tarski(esk4_0,k3_subset_1(esk3_0,esk5_0))
    & esk4_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_13,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_14,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_15,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | ~ m1_subset_1(X24,k1_zfmisc_1(X22))
      | ~ r1_tarski(X23,k3_subset_1(X22,X24))
      | r1_tarski(X24,k3_subset_1(X22,X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_subset_1])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X25,X26] :
      ( ( ~ r1_tarski(X26,k3_subset_1(X25,X26))
        | X26 = k1_subset_1(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(X25)) )
      & ( X26 != k1_subset_1(X25)
        | r1_tarski(X26,k3_subset_1(X25,X26))
        | ~ m1_subset_1(X26,k1_zfmisc_1(X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_subset_1])])])).

fof(c_0_21,plain,(
    ! [X21] : k1_subset_1(X21) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( r1_tarski(X3,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(esk3_0))
    | v1_xboole_0(k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,plain,
    ( X1 = k1_subset_1(X2)
    | ~ r1_tarski(X1,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X3,k3_subset_1(X2,X4))
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk5_0,esk3_0)
    | v1_xboole_0(k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_35,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk3_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk3_0))
    | ~ r1_tarski(X2,k3_subset_1(esk3_0,esk5_0))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk4_0,k3_subset_1(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk5_0,esk3_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k3_subset_1(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk3_0,esk4_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])]),c_0_45]),c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:38:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.42  # AutoSched0-Mode selected heuristic G_E___107_C41_F1_PI_AE_Q4_CS_SP_PS_S2U
% 0.18/0.42  # and selection function SelectNewComplexAHPExceptRRHorn.
% 0.18/0.42  #
% 0.18/0.42  # Preprocessing time       : 0.028 s
% 0.18/0.42  # Presaturation interreduction done
% 0.18/0.42  
% 0.18/0.42  # Proof found!
% 0.18/0.42  # SZS status Theorem
% 0.18/0.42  # SZS output start CNFRefutation
% 0.18/0.42  fof(t40_subset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 0.18/0.42  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.18/0.42  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.18/0.42  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.18/0.42  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.18/0.42  fof(t35_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X3))=>r1_tarski(X3,k3_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 0.18/0.42  fof(t38_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 0.18/0.42  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.18/0.42  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.18/0.42  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t40_subset_1])).
% 0.18/0.42  fof(c_0_10, plain, ![X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X14,X13)|r1_tarski(X14,X12)|X13!=k1_zfmisc_1(X12))&(~r1_tarski(X15,X12)|r2_hidden(X15,X13)|X13!=k1_zfmisc_1(X12)))&((~r2_hidden(esk2_2(X16,X17),X17)|~r1_tarski(esk2_2(X16,X17),X16)|X17=k1_zfmisc_1(X16))&(r2_hidden(esk2_2(X16,X17),X17)|r1_tarski(esk2_2(X16,X17),X16)|X17=k1_zfmisc_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.18/0.42  fof(c_0_11, plain, ![X19, X20]:(((~m1_subset_1(X20,X19)|r2_hidden(X20,X19)|v1_xboole_0(X19))&(~r2_hidden(X20,X19)|m1_subset_1(X20,X19)|v1_xboole_0(X19)))&((~m1_subset_1(X20,X19)|v1_xboole_0(X20)|~v1_xboole_0(X19))&(~v1_xboole_0(X20)|m1_subset_1(X20,X19)|~v1_xboole_0(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.18/0.42  fof(c_0_12, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))&((r1_tarski(esk4_0,esk5_0)&r1_tarski(esk4_0,k3_subset_1(esk3_0,esk5_0)))&esk4_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.18/0.42  fof(c_0_13, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.18/0.42  fof(c_0_14, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X9,X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.18/0.42  fof(c_0_15, plain, ![X22, X23, X24]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|(~m1_subset_1(X24,k1_zfmisc_1(X22))|(~r1_tarski(X23,k3_subset_1(X22,X24))|r1_tarski(X24,k3_subset_1(X22,X23))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_subset_1])])])).
% 0.18/0.42  cnf(c_0_16, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.42  cnf(c_0_17, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.42  cnf(c_0_18, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.42  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.42  fof(c_0_20, plain, ![X25, X26]:((~r1_tarski(X26,k3_subset_1(X25,X26))|X26=k1_subset_1(X25)|~m1_subset_1(X26,k1_zfmisc_1(X25)))&(X26!=k1_subset_1(X25)|r1_tarski(X26,k3_subset_1(X25,X26))|~m1_subset_1(X26,k1_zfmisc_1(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_subset_1])])])).
% 0.18/0.42  fof(c_0_21, plain, ![X21]:k1_subset_1(X21)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.18/0.42  cnf(c_0_22, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.42  cnf(c_0_23, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.42  cnf(c_0_24, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.42  cnf(c_0_25, plain, (r1_tarski(X3,k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.42  cnf(c_0_26, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_17])).
% 0.18/0.42  cnf(c_0_28, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(esk3_0))|v1_xboole_0(k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.42  cnf(c_0_29, plain, (X1=k1_subset_1(X2)|~r1_tarski(X1,k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.42  cnf(c_0_30, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.42  cnf(c_0_31, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.42  cnf(c_0_32, plain, (r1_tarski(X1,k3_subset_1(X2,X3))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X3,k3_subset_1(X2,X4))|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.42  cnf(c_0_33, plain, (~r1_tarski(X1,X2)|~v1_xboole_0(k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_23, c_0_26])).
% 0.18/0.42  cnf(c_0_34, negated_conjecture, (r1_tarski(esk5_0,esk3_0)|v1_xboole_0(k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.18/0.42  fof(c_0_35, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.18/0.42  cnf(c_0_36, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X1))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.18/0.42  cnf(c_0_37, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_26])).
% 0.18/0.42  cnf(c_0_38, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk3_0,X2))|~m1_subset_1(X2,k1_zfmisc_1(esk3_0))|~r1_tarski(X2,k3_subset_1(esk3_0,esk5_0))|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_19])).
% 0.18/0.42  cnf(c_0_39, negated_conjecture, (r1_tarski(esk4_0,k3_subset_1(esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.42  cnf(c_0_40, negated_conjecture, (r1_tarski(esk5_0,esk3_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.42  cnf(c_0_41, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.42  cnf(c_0_42, plain, (X1=k1_xboole_0|~r1_tarski(X1,k3_subset_1(X2,X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.18/0.42  cnf(c_0_43, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk3_0,esk4_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.18/0.42  cnf(c_0_44, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.42  cnf(c_0_45, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.42  cnf(c_0_46, negated_conjecture, (r1_tarski(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.18/0.42  cnf(c_0_47, negated_conjecture, (~r1_tarski(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])]), c_0_45]), c_0_37])).
% 0.18/0.42  cnf(c_0_48, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_24, c_0_46])).
% 0.18/0.42  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_44])]), ['proof']).
% 0.18/0.42  # SZS output end CNFRefutation
% 0.18/0.42  # Proof object total steps             : 50
% 0.18/0.42  # Proof object clause steps            : 31
% 0.18/0.42  # Proof object formula steps           : 19
% 0.18/0.42  # Proof object conjectures             : 16
% 0.18/0.42  # Proof object clause conjectures      : 13
% 0.18/0.42  # Proof object formula conjectures     : 3
% 0.18/0.42  # Proof object initial clauses used    : 14
% 0.18/0.42  # Proof object initial formulas used   : 9
% 0.18/0.42  # Proof object generating inferences   : 15
% 0.18/0.42  # Proof object simplifying inferences  : 8
% 0.18/0.42  # Training examples: 0 positive, 0 negative
% 0.18/0.42  # Parsed axioms                        : 9
% 0.18/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.42  # Initial clauses                      : 20
% 0.18/0.42  # Removed in clause preprocessing      : 1
% 0.18/0.42  # Initial clauses in saturation        : 19
% 0.18/0.42  # Processed clauses                    : 467
% 0.18/0.42  # ...of these trivial                  : 1
% 0.18/0.42  # ...subsumed                          : 170
% 0.18/0.42  # ...remaining for further processing  : 296
% 0.18/0.42  # Other redundant clauses eliminated   : 0
% 0.18/0.42  # Clauses deleted for lack of memory   : 0
% 0.18/0.42  # Backward-subsumed                    : 20
% 0.18/0.42  # Backward-rewritten                   : 6
% 0.18/0.42  # Generated clauses                    : 1943
% 0.18/0.42  # ...of the previous two non-trivial   : 1809
% 0.18/0.42  # Contextual simplify-reflections      : 6
% 0.18/0.42  # Paramodulations                      : 1938
% 0.18/0.42  # Factorizations                       : 2
% 0.18/0.42  # Equation resolutions                 : 3
% 0.18/0.42  # Propositional unsat checks           : 0
% 0.18/0.42  #    Propositional check models        : 0
% 0.18/0.42  #    Propositional check unsatisfiable : 0
% 0.18/0.42  #    Propositional clauses             : 0
% 0.18/0.42  #    Propositional clauses after purity: 0
% 0.18/0.42  #    Propositional unsat core size     : 0
% 0.18/0.42  #    Propositional preprocessing time  : 0.000
% 0.18/0.42  #    Propositional encoding time       : 0.000
% 0.18/0.42  #    Propositional solver time         : 0.000
% 0.18/0.42  #    Success case prop preproc time    : 0.000
% 0.18/0.42  #    Success case prop encoding time   : 0.000
% 0.18/0.42  #    Success case prop solver time     : 0.000
% 0.18/0.42  # Current number of processed clauses  : 251
% 0.18/0.42  #    Positive orientable unit clauses  : 7
% 0.18/0.42  #    Positive unorientable unit clauses: 0
% 0.18/0.42  #    Negative unit clauses             : 2
% 0.18/0.42  #    Non-unit-clauses                  : 242
% 0.18/0.42  # Current number of unprocessed clauses: 1348
% 0.18/0.42  # ...number of literals in the above   : 6400
% 0.18/0.42  # Current number of archived formulas  : 0
% 0.18/0.42  # Current number of archived clauses   : 46
% 0.18/0.42  # Clause-clause subsumption calls (NU) : 21148
% 0.18/0.42  # Rec. Clause-clause subsumption calls : 17326
% 0.18/0.42  # Non-unit clause-clause subsumptions  : 196
% 0.18/0.42  # Unit Clause-clause subsumption calls : 198
% 0.18/0.42  # Rewrite failures with RHS unbound    : 0
% 0.18/0.42  # BW rewrite match attempts            : 3
% 0.18/0.42  # BW rewrite match successes           : 3
% 0.18/0.42  # Condensation attempts                : 0
% 0.18/0.42  # Condensation successes               : 0
% 0.18/0.42  # Termbank termtop insertions          : 34352
% 0.18/0.42  
% 0.18/0.42  # -------------------------------------------------
% 0.18/0.42  # User time                : 0.081 s
% 0.18/0.42  # System time              : 0.005 s
% 0.18/0.42  # Total time               : 0.086 s
% 0.18/0.42  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
