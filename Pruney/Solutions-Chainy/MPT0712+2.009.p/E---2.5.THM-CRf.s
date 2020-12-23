%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:38 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 186 expanded)
%              Number of clauses        :   39 (  73 expanded)
%              Number of leaves         :   17 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  188 ( 373 expanded)
%              Number of equality atoms :   46 ( 120 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(t167_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k2_relat_1(k7_relat_1(X2,k1_tarski(X1))),k1_tarski(k1_funct_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

fof(fc23_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v4_relat_1(X3,X2) )
     => ( v1_relat_1(k7_relat_1(X3,X1))
        & v4_relat_1(k7_relat_1(X3,X1),X1)
        & v4_relat_1(k7_relat_1(X3,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t151_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(t95_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(t207_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_xboole_0(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X1),X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t118_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k1_relat_1(X3)) )
       => k9_relat_1(X3,k2_tarski(X1,X2)) = k2_tarski(k1_funct_1(X3,X1),k1_funct_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_17,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ r1_tarski(k1_relat_1(X37),X36)
      | k7_relat_1(X37,X36) = X37 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

fof(c_0_18,plain,(
    ! [X20,X21] :
      ( ( ~ v4_relat_1(X21,X20)
        | r1_tarski(k1_relat_1(X21),X20)
        | ~ v1_relat_1(X21) )
      & ( ~ r1_tarski(k1_relat_1(X21),X20)
        | v4_relat_1(X21,X20)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => r1_tarski(k2_relat_1(k7_relat_1(X2,k1_tarski(X1))),k1_tarski(k1_funct_1(X2,X1))) ) ),
    inference(assume_negation,[status(cth)],[t167_funct_1])).

cnf(c_0_20,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X24,X25,X26] :
      ( ( v1_relat_1(k7_relat_1(X26,X24))
        | ~ v1_relat_1(X26)
        | ~ v4_relat_1(X26,X25) )
      & ( v4_relat_1(k7_relat_1(X26,X24),X24)
        | ~ v1_relat_1(X26)
        | ~ v4_relat_1(X26,X25) )
      & ( v4_relat_1(k7_relat_1(X26,X24),X25)
        | ~ v1_relat_1(X26)
        | ~ v4_relat_1(X26,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc23_relat_1])])])).

fof(c_0_23,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | v1_relat_1(k7_relat_1(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_24,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & ~ r1_tarski(k2_relat_1(k7_relat_1(esk2_0,k1_tarski(esk1_0))),k1_tarski(k1_funct_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_25,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X11,X12,X13] : k2_enumset1(X11,X11,X12,X13) = k1_enumset1(X11,X12,X13) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X14,X15,X16,X17] : k3_enumset1(X14,X14,X15,X16,X17) = k2_enumset1(X14,X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | k2_relat_1(k7_relat_1(X28,X27)) = k9_relat_1(X28,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_30,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,plain,
    ( v4_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X18,X19] :
      ( r2_hidden(X18,X19)
      | r1_xboole_0(k1_tarski(X18),X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(esk2_0,k1_tarski(esk1_0))),k1_tarski(k1_funct_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,X2)
    | ~ v4_relat_1(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

fof(c_0_41,plain,(
    ! [X29,X30] :
      ( ( k9_relat_1(X30,X29) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X30),X29)
        | ~ v1_relat_1(X30) )
      & ( ~ r1_xboole_0(k1_relat_1(X30),X29)
        | k9_relat_1(X30,X29) = k1_xboole_0
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).

fof(c_0_42,plain,(
    ! [X34,X35] :
      ( ( k7_relat_1(X35,X34) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X35),X34)
        | ~ v1_relat_1(X35) )
      & ( ~ r1_xboole_0(k1_relat_1(X35),X34)
        | k7_relat_1(X35,X34) = k1_xboole_0
        | ~ v1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).

fof(c_0_43,plain,(
    ! [X31,X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ r1_xboole_0(X31,X32)
      | k7_relat_1(k7_relat_1(X33,X31),X32) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))),k3_enumset1(k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38])).

cnf(c_0_46,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v4_relat_1(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_48,plain,
    ( k9_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k7_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_50,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_51,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_35]),c_0_36]),c_0_37]),c_0_38])).

fof(c_0_53,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_relat_1(X40)
      | ~ v1_funct_1(X40)
      | ~ r2_hidden(X38,k1_relat_1(X40))
      | ~ r2_hidden(X39,k1_relat_1(X40))
      | k9_relat_1(X40,k2_tarski(X38,X39)) = k2_tarski(k1_funct_1(X40,X38),k1_funct_1(X40,X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_funct_1])])).

fof(c_0_54,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_55,negated_conjecture,
    ( ~ v4_relat_1(esk2_0,X1)
    | ~ r1_tarski(k9_relat_1(k7_relat_1(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)),X1),k3_enumset1(k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_56,plain,
    ( k9_relat_1(X1,X2) = k1_xboole_0
    | k7_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( k7_relat_1(k7_relat_1(X1,k3_enumset1(X2,X2,X2,X2,X2)),X3) = k1_xboole_0
    | r2_hidden(X2,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( k9_relat_1(X1,k2_tarski(X2,X3)) = k2_tarski(k1_funct_1(X1,X2),k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)),X1) != k1_xboole_0
    | ~ v4_relat_1(esk2_0,X1)
    | ~ v1_relat_1(k7_relat_1(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_62,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk2_0,k3_enumset1(X1,X1,X1,X1,X1)),X2) = k1_xboole_0
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_47])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)),k3_enumset1(k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_39]),c_0_47])])).

cnf(c_0_64,plain,
    ( k9_relat_1(X1,k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk1_0,X1)
    | ~ v4_relat_1(esk2_0,X1)
    | ~ v1_relat_1(k7_relat_1(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_66]),c_0_47])])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk1_0,X1)
    | ~ v4_relat_1(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_32]),c_0_47])])).

cnf(c_0_70,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_71,negated_conjecture,
    ( ~ v4_relat_1(esk2_0,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,plain,
    ( v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:39:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.45  #
% 0.21/0.45  # Preprocessing time       : 0.028 s
% 0.21/0.45  # Presaturation interreduction done
% 0.21/0.45  
% 0.21/0.45  # Proof found!
% 0.21/0.45  # SZS status Theorem
% 0.21/0.45  # SZS output start CNFRefutation
% 0.21/0.45  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.21/0.45  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.21/0.45  fof(t167_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k2_relat_1(k7_relat_1(X2,k1_tarski(X1))),k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_funct_1)).
% 0.21/0.45  fof(fc23_relat_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v4_relat_1(X3,X2))=>((v1_relat_1(k7_relat_1(X3,X1))&v4_relat_1(k7_relat_1(X3,X1),X1))&v4_relat_1(k7_relat_1(X3,X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 0.21/0.45  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.21/0.45  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.45  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.45  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.45  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.21/0.45  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.21/0.45  fof(t151_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 0.21/0.45  fof(t95_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 0.21/0.45  fof(t207_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_xboole_0(X1,X2)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 0.21/0.45  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.45  fof(t118_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k1_relat_1(X3)))=>k9_relat_1(X3,k2_tarski(X1,X2))=k2_tarski(k1_funct_1(X3,X1),k1_funct_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_funct_1)).
% 0.21/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.45  fof(c_0_17, plain, ![X36, X37]:(~v1_relat_1(X37)|(~r1_tarski(k1_relat_1(X37),X36)|k7_relat_1(X37,X36)=X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.21/0.45  fof(c_0_18, plain, ![X20, X21]:((~v4_relat_1(X21,X20)|r1_tarski(k1_relat_1(X21),X20)|~v1_relat_1(X21))&(~r1_tarski(k1_relat_1(X21),X20)|v4_relat_1(X21,X20)|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.21/0.45  fof(c_0_19, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k2_relat_1(k7_relat_1(X2,k1_tarski(X1))),k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t167_funct_1])).
% 0.21/0.45  cnf(c_0_20, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.45  cnf(c_0_21, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.45  fof(c_0_22, plain, ![X24, X25, X26]:(((v1_relat_1(k7_relat_1(X26,X24))|(~v1_relat_1(X26)|~v4_relat_1(X26,X25)))&(v4_relat_1(k7_relat_1(X26,X24),X24)|(~v1_relat_1(X26)|~v4_relat_1(X26,X25))))&(v4_relat_1(k7_relat_1(X26,X24),X25)|(~v1_relat_1(X26)|~v4_relat_1(X26,X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc23_relat_1])])])).
% 0.21/0.45  fof(c_0_23, plain, ![X22, X23]:(~v1_relat_1(X22)|v1_relat_1(k7_relat_1(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.21/0.45  fof(c_0_24, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&~r1_tarski(k2_relat_1(k7_relat_1(esk2_0,k1_tarski(esk1_0))),k1_tarski(k1_funct_1(esk2_0,esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.21/0.45  fof(c_0_25, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.45  fof(c_0_26, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.45  fof(c_0_27, plain, ![X11, X12, X13]:k2_enumset1(X11,X11,X12,X13)=k1_enumset1(X11,X12,X13), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.45  fof(c_0_28, plain, ![X14, X15, X16, X17]:k3_enumset1(X14,X14,X15,X16,X17)=k2_enumset1(X14,X15,X16,X17), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.45  fof(c_0_29, plain, ![X27, X28]:(~v1_relat_1(X28)|k2_relat_1(k7_relat_1(X28,X27))=k9_relat_1(X28,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.21/0.45  cnf(c_0_30, plain, (k7_relat_1(X1,X2)=X1|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.45  cnf(c_0_31, plain, (v4_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)|~v4_relat_1(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.45  cnf(c_0_32, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.45  fof(c_0_33, plain, ![X18, X19]:(r2_hidden(X18,X19)|r1_xboole_0(k1_tarski(X18),X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.21/0.45  cnf(c_0_34, negated_conjecture, (~r1_tarski(k2_relat_1(k7_relat_1(esk2_0,k1_tarski(esk1_0))),k1_tarski(k1_funct_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.45  cnf(c_0_35, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.45  cnf(c_0_36, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.45  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.45  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.45  cnf(c_0_39, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.45  cnf(c_0_40, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,X2)|~v4_relat_1(X1,X3)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.21/0.45  fof(c_0_41, plain, ![X29, X30]:((k9_relat_1(X30,X29)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X30),X29)|~v1_relat_1(X30))&(~r1_xboole_0(k1_relat_1(X30),X29)|k9_relat_1(X30,X29)=k1_xboole_0|~v1_relat_1(X30))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).
% 0.21/0.45  fof(c_0_42, plain, ![X34, X35]:((k7_relat_1(X35,X34)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X35),X34)|~v1_relat_1(X35))&(~r1_xboole_0(k1_relat_1(X35),X34)|k7_relat_1(X35,X34)=k1_xboole_0|~v1_relat_1(X35))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).
% 0.21/0.45  fof(c_0_43, plain, ![X31, X32, X33]:(~v1_relat_1(X33)|(~r1_xboole_0(X31,X32)|k7_relat_1(k7_relat_1(X33,X31),X32)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).
% 0.21/0.45  cnf(c_0_44, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.45  cnf(c_0_45, negated_conjecture, (~r1_tarski(k2_relat_1(k7_relat_1(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))),k3_enumset1(k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38])).
% 0.21/0.45  cnf(c_0_46, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(k7_relat_1(X1,X2),X3)|~v4_relat_1(X1,X3)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_32])).
% 0.21/0.45  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.45  cnf(c_0_48, plain, (k9_relat_1(X1,X2)=k1_xboole_0|~r1_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.45  cnf(c_0_49, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k7_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.45  fof(c_0_50, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.45  cnf(c_0_51, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.45  cnf(c_0_52, plain, (r2_hidden(X1,X2)|r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.21/0.45  fof(c_0_53, plain, ![X38, X39, X40]:(~v1_relat_1(X40)|~v1_funct_1(X40)|(~r2_hidden(X38,k1_relat_1(X40))|~r2_hidden(X39,k1_relat_1(X40))|k9_relat_1(X40,k2_tarski(X38,X39))=k2_tarski(k1_funct_1(X40,X38),k1_funct_1(X40,X39)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_funct_1])])).
% 0.21/0.45  fof(c_0_54, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.45  cnf(c_0_55, negated_conjecture, (~v4_relat_1(esk2_0,X1)|~r1_tarski(k9_relat_1(k7_relat_1(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)),X1),k3_enumset1(k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.21/0.45  cnf(c_0_56, plain, (k9_relat_1(X1,X2)=k1_xboole_0|k7_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.21/0.45  cnf(c_0_57, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.45  cnf(c_0_58, plain, (k7_relat_1(k7_relat_1(X1,k3_enumset1(X2,X2,X2,X2,X2)),X3)=k1_xboole_0|r2_hidden(X2,X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.45  cnf(c_0_59, plain, (k9_relat_1(X1,k2_tarski(X2,X3))=k2_tarski(k1_funct_1(X1,X2),k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.45  cnf(c_0_60, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.21/0.45  cnf(c_0_61, negated_conjecture, (k7_relat_1(k7_relat_1(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)),X1)!=k1_xboole_0|~v4_relat_1(esk2_0,X1)|~v1_relat_1(k7_relat_1(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.21/0.45  cnf(c_0_62, negated_conjecture, (k7_relat_1(k7_relat_1(esk2_0,k3_enumset1(X1,X1,X1,X1,X1)),X2)=k1_xboole_0|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_58, c_0_47])).
% 0.21/0.45  cnf(c_0_63, negated_conjecture, (~r1_tarski(k9_relat_1(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)),k3_enumset1(k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0),k1_funct_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_39]), c_0_47])])).
% 0.21/0.45  cnf(c_0_64, plain, (k9_relat_1(X1,k3_enumset1(X2,X2,X2,X2,X3))=k3_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))|~r2_hidden(X2,k1_relat_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38])).
% 0.21/0.45  cnf(c_0_65, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_60])).
% 0.21/0.45  cnf(c_0_66, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.45  cnf(c_0_67, negated_conjecture, (r2_hidden(esk1_0,X1)|~v4_relat_1(esk2_0,X1)|~v1_relat_1(k7_relat_1(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.21/0.45  cnf(c_0_68, negated_conjecture, (~r2_hidden(esk1_0,k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_66]), c_0_47])])).
% 0.21/0.45  cnf(c_0_69, negated_conjecture, (r2_hidden(esk1_0,X1)|~v4_relat_1(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_32]), c_0_47])])).
% 0.21/0.45  cnf(c_0_70, plain, (v4_relat_1(X1,X2)|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.45  cnf(c_0_71, negated_conjecture, (~v4_relat_1(esk2_0,k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.21/0.45  cnf(c_0_72, plain, (v4_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_70, c_0_65])).
% 0.21/0.45  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_47])]), ['proof']).
% 0.21/0.45  # SZS output end CNFRefutation
% 0.21/0.45  # Proof object total steps             : 74
% 0.21/0.45  # Proof object clause steps            : 39
% 0.21/0.45  # Proof object formula steps           : 35
% 0.21/0.45  # Proof object conjectures             : 16
% 0.21/0.45  # Proof object clause conjectures      : 13
% 0.21/0.45  # Proof object formula conjectures     : 3
% 0.21/0.45  # Proof object initial clauses used    : 20
% 0.21/0.45  # Proof object initial formulas used   : 17
% 0.21/0.45  # Proof object generating inferences   : 15
% 0.21/0.45  # Proof object simplifying inferences  : 35
% 0.21/0.45  # Training examples: 0 positive, 0 negative
% 0.21/0.45  # Parsed axioms                        : 17
% 0.21/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.45  # Initial clauses                      : 26
% 0.21/0.45  # Removed in clause preprocessing      : 4
% 0.21/0.45  # Initial clauses in saturation        : 22
% 0.21/0.45  # Processed clauses                    : 1088
% 0.21/0.45  # ...of these trivial                  : 8
% 0.21/0.45  # ...subsumed                          : 785
% 0.21/0.45  # ...remaining for further processing  : 295
% 0.21/0.45  # Other redundant clauses eliminated   : 20
% 0.21/0.45  # Clauses deleted for lack of memory   : 0
% 0.21/0.45  # Backward-subsumed                    : 61
% 0.21/0.45  # Backward-rewritten                   : 0
% 0.21/0.45  # Generated clauses                    : 2994
% 0.21/0.45  # ...of the previous two non-trivial   : 2824
% 0.21/0.45  # Contextual simplify-reflections      : 91
% 0.21/0.45  # Paramodulations                      : 2974
% 0.21/0.45  # Factorizations                       : 0
% 0.21/0.45  # Equation resolutions                 : 20
% 0.21/0.45  # Propositional unsat checks           : 0
% 0.21/0.45  #    Propositional check models        : 0
% 0.21/0.45  #    Propositional check unsatisfiable : 0
% 0.21/0.45  #    Propositional clauses             : 0
% 0.21/0.45  #    Propositional clauses after purity: 0
% 0.21/0.45  #    Propositional unsat core size     : 0
% 0.21/0.45  #    Propositional preprocessing time  : 0.000
% 0.21/0.45  #    Propositional encoding time       : 0.000
% 0.21/0.45  #    Propositional solver time         : 0.000
% 0.21/0.45  #    Success case prop preproc time    : 0.000
% 0.21/0.45  #    Success case prop encoding time   : 0.000
% 0.21/0.45  #    Success case prop solver time     : 0.000
% 0.21/0.45  # Current number of processed clauses  : 212
% 0.21/0.45  #    Positive orientable unit clauses  : 4
% 0.21/0.45  #    Positive unorientable unit clauses: 0
% 0.21/0.45  #    Negative unit clauses             : 7
% 0.21/0.45  #    Non-unit-clauses                  : 201
% 0.21/0.45  # Current number of unprocessed clauses: 1715
% 0.21/0.45  # ...number of literals in the above   : 8872
% 0.21/0.45  # Current number of archived formulas  : 0
% 0.21/0.45  # Current number of archived clauses   : 85
% 0.21/0.45  # Clause-clause subsumption calls (NU) : 40958
% 0.21/0.45  # Rec. Clause-clause subsumption calls : 10972
% 0.21/0.45  # Non-unit clause-clause subsumptions  : 918
% 0.21/0.45  # Unit Clause-clause subsumption calls : 224
% 0.21/0.45  # Rewrite failures with RHS unbound    : 0
% 0.21/0.45  # BW rewrite match attempts            : 4
% 0.21/0.45  # BW rewrite match successes           : 0
% 0.21/0.45  # Condensation attempts                : 0
% 0.21/0.45  # Condensation successes               : 0
% 0.21/0.45  # Termbank termtop insertions          : 45963
% 0.21/0.46  
% 0.21/0.46  # -------------------------------------------------
% 0.21/0.46  # User time                : 0.103 s
% 0.21/0.46  # System time              : 0.004 s
% 0.21/0.46  # Total time               : 0.107 s
% 0.21/0.46  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
