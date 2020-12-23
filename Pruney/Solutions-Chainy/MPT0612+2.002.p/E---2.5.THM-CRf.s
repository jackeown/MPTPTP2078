%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:40 EST 2020

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   42 (  61 expanded)
%              Number of clauses        :   23 (  28 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 127 expanded)
%              Number of equality atoms :   30 (  46 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t216_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

fof(t109_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t207_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_xboole_0(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X1),X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(c_0_9,plain,(
    ! [X28,X29,X30] :
      ( ~ r1_tarski(X28,X29)
      | r1_xboole_0(X28,k4_xboole_0(X30,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

fof(c_0_10,plain,(
    ! [X26,X27] :
      ( ( ~ r1_xboole_0(X26,X27)
        | k4_xboole_0(X26,X27) = X26 )
      & ( k4_xboole_0(X26,X27) != X26
        | r1_xboole_0(X26,X27) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t216_relat_1])).

fof(c_0_12,plain,(
    ! [X37,X38,X39] :
      ( ~ v1_relat_1(X39)
      | k7_relat_1(X39,k6_subset_1(X37,X38)) = k6_subset_1(k7_relat_1(X39,X37),k7_relat_1(X39,X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_relat_1])])).

fof(c_0_13,plain,(
    ! [X33,X34] : k6_subset_1(X33,X34) = k4_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_14,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & r1_tarski(esk3_0,esk4_0)
    & k7_relat_1(k6_subset_1(esk5_0,k7_relat_1(esk5_0,esk4_0)),esk3_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_18,plain,
    ( k7_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X43] :
      ( ~ v1_relat_1(X43)
      | k7_relat_1(X43,k1_relat_1(X43)) = X43 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X24,X25] : r1_xboole_0(k4_xboole_0(X24,X25),X25) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_25,plain,(
    ! [X40,X41,X42] :
      ( ~ v1_relat_1(X42)
      | ~ r1_xboole_0(X40,X41)
      | k7_relat_1(k7_relat_1(X42,X40),X41) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).

cnf(c_0_26,plain,
    ( k7_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_19])).

cnf(c_0_27,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r1_xboole_0(esk3_0,X1)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),X2)) = k4_xboole_0(X1,k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_xboole_0(esk3_0,k4_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k7_relat_1(k6_subset_1(esk5_0,k7_relat_1(esk5_0,esk4_0)),esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,plain,
    ( k7_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X2)),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k4_xboole_0(k1_relat_1(X1),X2),X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( k7_relat_1(k4_xboole_0(esk5_0,k7_relat_1(esk5_0,esk4_0)),esk3_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_35,c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( k7_relat_1(k4_xboole_0(X1,k7_relat_1(X1,esk4_0)),esk3_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.71/0.88  # AutoSched0-Mode selected heuristic G_____0016_5gdfifo
% 0.71/0.88  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.71/0.88  #
% 0.71/0.88  # Preprocessing time       : 0.028 s
% 0.71/0.88  
% 0.71/0.88  # Proof found!
% 0.71/0.88  # SZS status Theorem
% 0.71/0.88  # SZS output start CNFRefutation
% 0.71/0.88  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.71/0.88  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.71/0.88  fof(t216_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 0.71/0.88  fof(t109_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k7_relat_1(X3,X1),k7_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_relat_1)).
% 0.71/0.88  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.71/0.88  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.71/0.88  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 0.71/0.88  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.71/0.88  fof(t207_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_xboole_0(X1,X2)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 0.71/0.88  fof(c_0_9, plain, ![X28, X29, X30]:(~r1_tarski(X28,X29)|r1_xboole_0(X28,k4_xboole_0(X30,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.71/0.88  fof(c_0_10, plain, ![X26, X27]:((~r1_xboole_0(X26,X27)|k4_xboole_0(X26,X27)=X26)&(k4_xboole_0(X26,X27)!=X26|r1_xboole_0(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.71/0.88  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t216_relat_1])).
% 0.71/0.88  fof(c_0_12, plain, ![X37, X38, X39]:(~v1_relat_1(X39)|k7_relat_1(X39,k6_subset_1(X37,X38))=k6_subset_1(k7_relat_1(X39,X37),k7_relat_1(X39,X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_relat_1])])).
% 0.71/0.88  fof(c_0_13, plain, ![X33, X34]:k6_subset_1(X33,X34)=k4_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.71/0.88  fof(c_0_14, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.71/0.88  cnf(c_0_15, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.71/0.88  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.71/0.88  fof(c_0_17, negated_conjecture, (v1_relat_1(esk5_0)&(r1_tarski(esk3_0,esk4_0)&k7_relat_1(k6_subset_1(esk5_0,k7_relat_1(esk5_0,esk4_0)),esk3_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.71/0.88  cnf(c_0_18, plain, (k7_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.71/0.88  cnf(c_0_19, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.71/0.88  fof(c_0_20, plain, ![X43]:(~v1_relat_1(X43)|k7_relat_1(X43,k1_relat_1(X43))=X43), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.71/0.88  cnf(c_0_21, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.71/0.88  cnf(c_0_22, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.71/0.88  cnf(c_0_23, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.71/0.88  fof(c_0_24, plain, ![X24, X25]:r1_xboole_0(k4_xboole_0(X24,X25),X25), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.71/0.88  fof(c_0_25, plain, ![X40, X41, X42]:(~v1_relat_1(X42)|(~r1_xboole_0(X40,X41)|k7_relat_1(k7_relat_1(X42,X40),X41)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).
% 0.71/0.88  cnf(c_0_26, plain, (k7_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_19])).
% 0.71/0.88  cnf(c_0_27, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.71/0.88  cnf(c_0_28, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_21])).
% 0.71/0.88  cnf(c_0_29, negated_conjecture, (r1_xboole_0(esk3_0,X1)|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.71/0.88  cnf(c_0_30, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.71/0.88  cnf(c_0_31, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.71/0.88  cnf(c_0_32, plain, (k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),X2))=k4_xboole_0(X1,k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.71/0.88  cnf(c_0_33, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_22, c_0_28])).
% 0.71/0.88  cnf(c_0_34, negated_conjecture, (r1_xboole_0(esk3_0,k4_xboole_0(X1,esk4_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.71/0.88  cnf(c_0_35, negated_conjecture, (k7_relat_1(k6_subset_1(esk5_0,k7_relat_1(esk5_0,esk4_0)),esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.71/0.88  cnf(c_0_36, plain, (k7_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X2)),X3)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(k4_xboole_0(k1_relat_1(X1),X2),X3)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.71/0.88  cnf(c_0_37, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.71/0.88  cnf(c_0_38, negated_conjecture, (k7_relat_1(k4_xboole_0(esk5_0,k7_relat_1(esk5_0,esk4_0)),esk3_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_35, c_0_19])).
% 0.71/0.88  cnf(c_0_39, negated_conjecture, (k7_relat_1(k4_xboole_0(X1,k7_relat_1(X1,esk4_0)),esk3_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.71/0.88  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.71/0.88  cnf(c_0_41, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])]), ['proof']).
% 0.71/0.88  # SZS output end CNFRefutation
% 0.71/0.88  # Proof object total steps             : 42
% 0.71/0.88  # Proof object clause steps            : 23
% 0.71/0.88  # Proof object formula steps           : 19
% 0.71/0.88  # Proof object conjectures             : 12
% 0.71/0.88  # Proof object clause conjectures      : 9
% 0.71/0.88  # Proof object formula conjectures     : 3
% 0.71/0.88  # Proof object initial clauses used    : 11
% 0.71/0.88  # Proof object initial formulas used   : 9
% 0.71/0.88  # Proof object generating inferences   : 9
% 0.71/0.88  # Proof object simplifying inferences  : 6
% 0.71/0.88  # Training examples: 0 positive, 0 negative
% 0.71/0.88  # Parsed axioms                        : 16
% 0.71/0.88  # Removed by relevancy pruning/SinE    : 0
% 0.71/0.88  # Initial clauses                      : 25
% 0.71/0.88  # Removed in clause preprocessing      : 2
% 0.71/0.88  # Initial clauses in saturation        : 23
% 0.71/0.88  # Processed clauses                    : 4899
% 0.71/0.88  # ...of these trivial                  : 37
% 0.71/0.88  # ...subsumed                          : 4028
% 0.71/0.88  # ...remaining for further processing  : 834
% 0.71/0.88  # Other redundant clauses eliminated   : 3
% 0.71/0.88  # Clauses deleted for lack of memory   : 0
% 0.71/0.88  # Backward-subsumed                    : 72
% 0.71/0.88  # Backward-rewritten                   : 32
% 0.71/0.88  # Generated clauses                    : 60631
% 0.71/0.88  # ...of the previous two non-trivial   : 46881
% 0.71/0.88  # Contextual simplify-reflections      : 2
% 0.71/0.88  # Paramodulations                      : 60628
% 0.71/0.88  # Factorizations                       : 0
% 0.71/0.88  # Equation resolutions                 : 3
% 0.71/0.88  # Propositional unsat checks           : 0
% 0.71/0.88  #    Propositional check models        : 0
% 0.71/0.88  #    Propositional check unsatisfiable : 0
% 0.71/0.88  #    Propositional clauses             : 0
% 0.71/0.88  #    Propositional clauses after purity: 0
% 0.71/0.88  #    Propositional unsat core size     : 0
% 0.71/0.88  #    Propositional preprocessing time  : 0.000
% 0.71/0.88  #    Propositional encoding time       : 0.000
% 0.71/0.88  #    Propositional solver time         : 0.000
% 0.71/0.88  #    Success case prop preproc time    : 0.000
% 0.71/0.88  #    Success case prop encoding time   : 0.000
% 0.71/0.88  #    Success case prop solver time     : 0.000
% 0.71/0.88  # Current number of processed clauses  : 728
% 0.71/0.88  #    Positive orientable unit clauses  : 60
% 0.71/0.88  #    Positive unorientable unit clauses: 1
% 0.71/0.88  #    Negative unit clauses             : 4
% 0.71/0.88  #    Non-unit-clauses                  : 663
% 0.71/0.88  # Current number of unprocessed clauses: 41495
% 0.71/0.88  # ...number of literals in the above   : 165186
% 0.71/0.88  # Current number of archived formulas  : 0
% 0.71/0.88  # Current number of archived clauses   : 106
% 0.71/0.88  # Clause-clause subsumption calls (NU) : 56792
% 0.71/0.88  # Rec. Clause-clause subsumption calls : 41511
% 0.71/0.88  # Non-unit clause-clause subsumptions  : 2714
% 0.71/0.88  # Unit Clause-clause subsumption calls : 597
% 0.71/0.88  # Rewrite failures with RHS unbound    : 0
% 0.71/0.88  # BW rewrite match attempts            : 123
% 0.71/0.88  # BW rewrite match successes           : 19
% 0.71/0.88  # Condensation attempts                : 0
% 0.71/0.88  # Condensation successes               : 0
% 0.71/0.88  # Termbank termtop insertions          : 1061171
% 0.71/0.88  
% 0.71/0.88  # -------------------------------------------------
% 0.71/0.88  # User time                : 0.515 s
% 0.71/0.88  # System time              : 0.019 s
% 0.71/0.88  # Total time               : 0.534 s
% 0.71/0.88  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
