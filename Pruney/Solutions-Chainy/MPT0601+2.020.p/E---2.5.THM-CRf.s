%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:15 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 131 expanded)
%              Number of clauses        :   28 (  59 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  122 ( 422 expanded)
%              Number of equality atoms :   33 ( 117 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t151_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t55_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(c_0_9,plain,(
    ! [X15,X16,X17,X19,X20,X21,X22,X24] :
      ( ( ~ r2_hidden(X17,X16)
        | r2_hidden(k4_tarski(X17,esk2_3(X15,X16,X17)),X15)
        | X16 != k1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X19,X20),X15)
        | r2_hidden(X19,X16)
        | X16 != k1_relat_1(X15) )
      & ( ~ r2_hidden(esk3_2(X21,X22),X22)
        | ~ r2_hidden(k4_tarski(esk3_2(X21,X22),X24),X21)
        | X22 = k1_relat_1(X21) )
      & ( r2_hidden(esk3_2(X21,X22),X22)
        | r2_hidden(k4_tarski(esk3_2(X21,X22),esk4_2(X21,X22)),X21)
        | X22 = k1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_10,plain,(
    ! [X28,X29,X30] :
      ( ( ~ r2_hidden(k4_tarski(X28,X29),X30)
        | r2_hidden(X29,k11_relat_1(X30,X28))
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(X29,k11_relat_1(X30,X28))
        | r2_hidden(k4_tarski(X28,X29),X30)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_11,plain,(
    ! [X7] :
      ( X7 = k1_xboole_0
      | r2_hidden(esk1_1(X7),X7) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & ( ~ r2_hidden(esk5_0,k1_relat_1(esk6_0))
      | k11_relat_1(esk6_0,esk5_0) = k1_xboole_0 )
    & ( r2_hidden(esk5_0,k1_relat_1(esk6_0))
      | k11_relat_1(esk6_0,esk5_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(X2,esk1_1(k11_relat_1(X1,X2))),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0))
    | k11_relat_1(esk6_0,esk5_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | k11_relat_1(X13,X14) = k9_relat_1(X13,k1_tarski(X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_23,plain,(
    ! [X9] : k2_tarski(X9,X9) = k1_tarski(X9) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_24,negated_conjecture,
    ( k11_relat_1(esk6_0,esk5_0) = k1_xboole_0
    | ~ r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

fof(c_0_26,plain,(
    ! [X26,X27] :
      ( ( k9_relat_1(X27,X26) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X27),X26)
        | ~ v1_relat_1(X27) )
      & ( ~ r1_xboole_0(k1_relat_1(X27),X26)
        | k9_relat_1(X27,X26) = k1_xboole_0
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).

cnf(c_0_27,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( k11_relat_1(esk6_0,esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_32,plain,(
    ! [X5,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_33,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k9_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k2_tarski(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(k4_tarski(esk5_0,X1),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_21])])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_xboole_0(k2_tarski(X10,X11),X12)
      | ~ r2_hidden(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r1_xboole_0(k1_relat_1(X1),k2_tarski(X2,X2))
    | k11_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_20]),c_0_17])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_25])])).

cnf(c_0_42,plain,
    ( ~ r1_xboole_0(k2_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( r1_xboole_0(k2_tarski(X1,X1),k1_relat_1(X2))
    | k11_relat_1(X2,X1) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( k11_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_30]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.48  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.21/0.48  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.48  #
% 0.21/0.48  # Preprocessing time       : 0.027 s
% 0.21/0.48  
% 0.21/0.48  # Proof found!
% 0.21/0.48  # SZS status Theorem
% 0.21/0.48  # SZS output start CNFRefutation
% 0.21/0.48  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.21/0.48  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.21/0.48  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.21/0.48  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 0.21/0.48  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 0.21/0.48  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.48  fof(t151_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 0.21/0.48  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.21/0.48  fof(t55_zfmisc_1, axiom, ![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 0.21/0.48  fof(c_0_9, plain, ![X15, X16, X17, X19, X20, X21, X22, X24]:(((~r2_hidden(X17,X16)|r2_hidden(k4_tarski(X17,esk2_3(X15,X16,X17)),X15)|X16!=k1_relat_1(X15))&(~r2_hidden(k4_tarski(X19,X20),X15)|r2_hidden(X19,X16)|X16!=k1_relat_1(X15)))&((~r2_hidden(esk3_2(X21,X22),X22)|~r2_hidden(k4_tarski(esk3_2(X21,X22),X24),X21)|X22=k1_relat_1(X21))&(r2_hidden(esk3_2(X21,X22),X22)|r2_hidden(k4_tarski(esk3_2(X21,X22),esk4_2(X21,X22)),X21)|X22=k1_relat_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.21/0.48  fof(c_0_10, plain, ![X28, X29, X30]:((~r2_hidden(k4_tarski(X28,X29),X30)|r2_hidden(X29,k11_relat_1(X30,X28))|~v1_relat_1(X30))&(~r2_hidden(X29,k11_relat_1(X30,X28))|r2_hidden(k4_tarski(X28,X29),X30)|~v1_relat_1(X30))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.21/0.48  fof(c_0_11, plain, ![X7]:(X7=k1_xboole_0|r2_hidden(esk1_1(X7),X7)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.21/0.48  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 0.21/0.48  cnf(c_0_13, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.48  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.48  cnf(c_0_15, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.48  fof(c_0_16, negated_conjecture, (v1_relat_1(esk6_0)&((~r2_hidden(esk5_0,k1_relat_1(esk6_0))|k11_relat_1(esk6_0,esk5_0)=k1_xboole_0)&(r2_hidden(esk5_0,k1_relat_1(esk6_0))|k11_relat_1(esk6_0,esk5_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.21/0.48  cnf(c_0_17, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_13])).
% 0.21/0.48  cnf(c_0_18, plain, (k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(X2,esk1_1(k11_relat_1(X1,X2))),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.21/0.48  cnf(c_0_19, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))|k11_relat_1(esk6_0,esk5_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.48  cnf(c_0_20, plain, (k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.48  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.48  fof(c_0_22, plain, ![X13, X14]:(~v1_relat_1(X13)|k11_relat_1(X13,X14)=k9_relat_1(X13,k1_tarski(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.21/0.48  fof(c_0_23, plain, ![X9]:k2_tarski(X9,X9)=k1_tarski(X9), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.48  cnf(c_0_24, negated_conjecture, (k11_relat_1(esk6_0,esk5_0)=k1_xboole_0|~r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.48  cnf(c_0_25, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.21/0.48  fof(c_0_26, plain, ![X26, X27]:((k9_relat_1(X27,X26)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X27),X26)|~v1_relat_1(X27))&(~r1_xboole_0(k1_relat_1(X27),X26)|k9_relat_1(X27,X26)=k1_xboole_0|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).
% 0.21/0.48  cnf(c_0_27, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.48  cnf(c_0_28, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.48  cnf(c_0_29, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.48  cnf(c_0_30, negated_conjecture, (k11_relat_1(esk6_0,esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25])])).
% 0.21/0.48  cnf(c_0_31, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.48  fof(c_0_32, plain, ![X5, X6]:(~r1_xboole_0(X5,X6)|r1_xboole_0(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.21/0.48  cnf(c_0_33, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k9_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.48  cnf(c_0_34, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k2_tarski(X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.48  cnf(c_0_35, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~r2_hidden(k4_tarski(esk5_0,X1),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_21])])).
% 0.21/0.48  cnf(c_0_36, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_31])).
% 0.21/0.48  fof(c_0_37, plain, ![X10, X11, X12]:(~r1_xboole_0(k2_tarski(X10,X11),X12)|~r2_hidden(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).
% 0.21/0.48  cnf(c_0_38, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.48  cnf(c_0_39, plain, (r1_xboole_0(k1_relat_1(X1),k2_tarski(X2,X2))|k11_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.48  cnf(c_0_40, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X3,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_20]), c_0_17])).
% 0.21/0.48  cnf(c_0_41, negated_conjecture, (r2_hidden(esk2_3(esk6_0,k1_relat_1(esk6_0),esk5_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_25])])).
% 0.21/0.48  cnf(c_0_42, plain, (~r1_xboole_0(k2_tarski(X1,X2),X3)|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.48  cnf(c_0_43, plain, (r1_xboole_0(k2_tarski(X1,X1),k1_relat_1(X2))|k11_relat_1(X2,X1)!=k1_xboole_0|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.48  cnf(c_0_44, negated_conjecture, (r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.21/0.48  cnf(c_0_45, plain, (k11_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.21/0.48  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_30]), c_0_21])]), ['proof']).
% 0.21/0.48  # SZS output end CNFRefutation
% 0.21/0.48  # Proof object total steps             : 47
% 0.21/0.48  # Proof object clause steps            : 28
% 0.21/0.48  # Proof object formula steps           : 19
% 0.21/0.48  # Proof object conjectures             : 12
% 0.21/0.48  # Proof object clause conjectures      : 9
% 0.21/0.48  # Proof object formula conjectures     : 3
% 0.21/0.48  # Proof object initial clauses used    : 13
% 0.21/0.48  # Proof object initial formulas used   : 9
% 0.21/0.48  # Proof object generating inferences   : 11
% 0.21/0.48  # Proof object simplifying inferences  : 15
% 0.21/0.48  # Training examples: 0 positive, 0 negative
% 0.21/0.48  # Parsed axioms                        : 9
% 0.21/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.48  # Initial clauses                      : 16
% 0.21/0.48  # Removed in clause preprocessing      : 1
% 0.21/0.48  # Initial clauses in saturation        : 15
% 0.21/0.48  # Processed clauses                    : 611
% 0.21/0.48  # ...of these trivial                  : 28
% 0.21/0.48  # ...subsumed                          : 421
% 0.21/0.48  # ...remaining for further processing  : 162
% 0.21/0.48  # Other redundant clauses eliminated   : 2
% 0.21/0.48  # Clauses deleted for lack of memory   : 0
% 0.21/0.48  # Backward-subsumed                    : 15
% 0.21/0.48  # Backward-rewritten                   : 12
% 0.21/0.48  # Generated clauses                    : 9635
% 0.21/0.48  # ...of the previous two non-trivial   : 6872
% 0.21/0.48  # Contextual simplify-reflections      : 2
% 0.21/0.48  # Paramodulations                      : 9631
% 0.21/0.48  # Factorizations                       : 2
% 0.21/0.48  # Equation resolutions                 : 2
% 0.21/0.48  # Propositional unsat checks           : 0
% 0.21/0.48  #    Propositional check models        : 0
% 0.21/0.48  #    Propositional check unsatisfiable : 0
% 0.21/0.48  #    Propositional clauses             : 0
% 0.21/0.48  #    Propositional clauses after purity: 0
% 0.21/0.48  #    Propositional unsat core size     : 0
% 0.21/0.48  #    Propositional preprocessing time  : 0.000
% 0.21/0.48  #    Propositional encoding time       : 0.000
% 0.21/0.48  #    Propositional solver time         : 0.000
% 0.21/0.48  #    Success case prop preproc time    : 0.000
% 0.21/0.48  #    Success case prop encoding time   : 0.000
% 0.21/0.48  #    Success case prop solver time     : 0.000
% 0.21/0.48  # Current number of processed clauses  : 133
% 0.21/0.48  #    Positive orientable unit clauses  : 5
% 0.21/0.48  #    Positive unorientable unit clauses: 0
% 0.21/0.48  #    Negative unit clauses             : 0
% 0.21/0.48  #    Non-unit-clauses                  : 128
% 0.21/0.48  # Current number of unprocessed clauses: 6266
% 0.21/0.48  # ...number of literals in the above   : 25283
% 0.21/0.48  # Current number of archived formulas  : 0
% 0.21/0.48  # Current number of archived clauses   : 28
% 0.21/0.48  # Clause-clause subsumption calls (NU) : 4521
% 0.21/0.48  # Rec. Clause-clause subsumption calls : 4449
% 0.21/0.48  # Non-unit clause-clause subsumptions  : 438
% 0.21/0.48  # Unit Clause-clause subsumption calls : 0
% 0.21/0.48  # Rewrite failures with RHS unbound    : 0
% 0.21/0.48  # BW rewrite match attempts            : 44
% 0.21/0.48  # BW rewrite match successes           : 4
% 0.21/0.48  # Condensation attempts                : 0
% 0.21/0.48  # Condensation successes               : 0
% 0.21/0.48  # Termbank termtop insertions          : 169113
% 0.21/0.48  
% 0.21/0.48  # -------------------------------------------------
% 0.21/0.48  # User time                : 0.127 s
% 0.21/0.48  # System time              : 0.005 s
% 0.21/0.48  # Total time               : 0.132 s
% 0.21/0.48  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
