%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:02 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 401 expanded)
%              Number of clauses        :   66 ( 183 expanded)
%              Number of leaves         :   15 ( 104 expanded)
%              Depth                    :   20
%              Number of atoms          :  196 ( 790 expanded)
%              Number of equality atoms :   63 ( 289 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_16,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))
    & r2_hidden(esk6_0,esk5_0)
    & r1_xboole_0(esk5_0,esk4_0)
    & ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_17,plain,(
    ! [X36] : k2_tarski(X36,X36) = k1_tarski(X36) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X37,X38] : k1_enumset1(X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X39,X40,X41] : k2_enumset1(X39,X39,X40,X41) = k1_enumset1(X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k4_xboole_0(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_21,plain,(
    ! [X26,X27,X28] :
      ( ~ r1_tarski(X26,X27)
      | ~ r1_xboole_0(X27,X28)
      | r1_xboole_0(X26,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X14,X15] :
      ( ~ r1_xboole_0(X14,X15)
      | r1_xboole_0(X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_28,plain,(
    ! [X32,X33] : r1_xboole_0(k4_xboole_0(X32,X33),X33) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_29,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X44,X45] :
      ( ( k4_xboole_0(X44,k1_tarski(X45)) != X44
        | ~ r2_hidden(X45,X44) )
      & ( r2_hidden(X45,X44)
        | k4_xboole_0(X44,k1_tarski(X45)) = X44 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_36,plain,(
    ! [X34,X35] :
      ( ( ~ r1_xboole_0(X34,X35)
        | k4_xboole_0(X34,X35) = X34 )
      & ( k4_xboole_0(X34,X35) != X34
        | r1_xboole_0(X34,X35) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_37,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),X1)
    | ~ r1_xboole_0(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_42,plain,(
    ! [X22,X23] : k4_xboole_0(X22,k3_xboole_0(X22,X23)) = k4_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k4_xboole_0(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk5_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) = k4_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_47,c_0_26])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(X1,esk5_0)) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)) = X1
    | ~ r2_hidden(X2,k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) = k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))) = k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_57,plain,(
    ! [X16,X17,X19,X20,X21] :
      ( ( r1_xboole_0(X16,X17)
        | r2_hidden(esk2_2(X16,X17),k3_xboole_0(X16,X17)) )
      & ( ~ r2_hidden(X21,k3_xboole_0(X19,X20))
        | ~ r1_xboole_0(X19,X20) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_59,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_33])).

cnf(c_0_60,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k2_enumset1(X3,X3,X3,X3)) = k4_xboole_0(X1,X2)
    | k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)) = X2 ),
    inference(spm,[status(thm)],[c_0_53,c_0_46])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) = k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk5_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_56])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,esk4_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) = k4_xboole_0(esk3_0,esk4_0)
    | k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk5_0) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk5_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_63])).

cnf(c_0_69,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_64,c_0_26])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk5_0) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))
    | ~ r2_hidden(esk6_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)) = X1
    | r2_hidden(X2,k4_xboole_0(X1,X3))
    | r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_67,c_0_46])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_68])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2)))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_38])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_44])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk5_0) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))
    | k4_xboole_0(esk3_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

fof(c_0_76,plain,(
    ! [X42,X43] : k3_tarski(k2_tarski(X42,X43)) = k2_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_77,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_50])).

cnf(c_0_78,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk5_0) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))
    | r1_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_79,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_80,plain,(
    ! [X29,X30,X31] :
      ( ( r1_xboole_0(X29,k2_xboole_0(X30,X31))
        | ~ r1_xboole_0(X29,X30)
        | ~ r1_xboole_0(X29,X31) )
      & ( r1_xboole_0(X29,X30)
        | ~ r1_xboole_0(X29,k2_xboole_0(X30,X31)) )
      & ( r1_xboole_0(X29,X31)
        | ~ r1_xboole_0(X29,k2_xboole_0(X30,X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_81,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_55])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk5_0) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))
    | k4_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_78]),c_0_50])).

cnf(c_0_84,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_79,c_0_26])).

cnf(c_0_85,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_86,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_81,c_0_24])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk3_0
    | ~ r2_hidden(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_84])).

cnf(c_0_89,plain,
    ( r1_xboole_0(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3)))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86]),c_0_25])).

cnf(c_0_90,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( r1_xboole_0(esk4_0,k3_tarski(k2_enumset1(X1,X1,X1,esk5_0)))
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_63])).

cnf(c_0_92,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_94,negated_conjecture,
    ( r1_xboole_0(esk4_0,k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0)),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_86]),c_0_25])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_94]),c_0_95]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.20/0.41  # and selection function SelectCQArNTNpEqFirst.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.028 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.20/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.41  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.41  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.41  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.20/0.41  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.41  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.41  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.41  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.20/0.41  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.41  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.20/0.41  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.41  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.41  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.20/0.41  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.20/0.41  fof(c_0_16, negated_conjecture, (((r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))&r2_hidden(esk6_0,esk5_0))&r1_xboole_0(esk5_0,esk4_0))&~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.20/0.41  fof(c_0_17, plain, ![X36]:k2_tarski(X36,X36)=k1_tarski(X36), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.41  fof(c_0_18, plain, ![X37, X38]:k1_enumset1(X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.41  fof(c_0_19, plain, ![X39, X40, X41]:k2_enumset1(X39,X39,X40,X41)=k1_enumset1(X39,X40,X41), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.41  fof(c_0_20, plain, ![X24, X25]:k4_xboole_0(X24,k4_xboole_0(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.41  fof(c_0_21, plain, ![X26, X27, X28]:(~r1_tarski(X26,X27)|~r1_xboole_0(X27,X28)|r1_xboole_0(X26,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.20/0.41  cnf(c_0_22, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  fof(c_0_27, plain, ![X14, X15]:(~r1_xboole_0(X14,X15)|r1_xboole_0(X15,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.41  fof(c_0_28, plain, ![X32, X33]:r1_xboole_0(k4_xboole_0(X32,X33),X33), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.42  fof(c_0_29, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.42  cnf(c_0_30, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_31, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 0.20/0.42  cnf(c_0_32, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.42  cnf(c_0_33, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.42  cnf(c_0_34, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.42  fof(c_0_35, plain, ![X44, X45]:((k4_xboole_0(X44,k1_tarski(X45))!=X44|~r2_hidden(X45,X44))&(r2_hidden(X45,X44)|k4_xboole_0(X44,k1_tarski(X45))=X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.20/0.42  fof(c_0_36, plain, ![X34, X35]:((~r1_xboole_0(X34,X35)|k4_xboole_0(X34,X35)=X34)&(k4_xboole_0(X34,X35)!=X34|r1_xboole_0(X34,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.42  cnf(c_0_37, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),X1)|~r1_xboole_0(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.42  cnf(c_0_38, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.42  cnf(c_0_39, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_34])).
% 0.20/0.42  cnf(c_0_40, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_41, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.42  fof(c_0_42, plain, ![X22, X23]:k4_xboole_0(X22,k3_xboole_0(X22,X23))=k4_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.20/0.42  cnf(c_0_43, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.42  cnf(c_0_44, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.42  cnf(c_0_45, negated_conjecture, (~r2_hidden(esk6_0,k4_xboole_0(X1,esk5_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.42  cnf(c_0_46, plain, (k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_23]), c_0_24]), c_0_25])).
% 0.20/0.42  cnf(c_0_47, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.42  cnf(c_0_48, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.42  cnf(c_0_49, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk5_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))=k4_xboole_0(X1,esk5_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.42  cnf(c_0_50, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_47, c_0_26])).
% 0.20/0.42  cnf(c_0_51, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(X1,esk5_0))=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.42  cnf(c_0_52, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.42  cnf(c_0_53, plain, (k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))=X1|~r2_hidden(X2,k4_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_39, c_0_46])).
% 0.20/0.42  cnf(c_0_54, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))=k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_50, c_0_48])).
% 0.20/0.42  cnf(c_0_55, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))=k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk5_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.42  cnf(c_0_56, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  fof(c_0_57, plain, ![X16, X17, X19, X20, X21]:((r1_xboole_0(X16,X17)|r2_hidden(esk2_2(X16,X17),k3_xboole_0(X16,X17)))&(~r2_hidden(X21,k3_xboole_0(X19,X20))|~r1_xboole_0(X19,X20))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.42  cnf(c_0_58, plain, (k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_23]), c_0_24]), c_0_25])).
% 0.20/0.42  cnf(c_0_59, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_43, c_0_33])).
% 0.20/0.42  cnf(c_0_60, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k2_enumset1(X3,X3,X3,X3))=k4_xboole_0(X1,X2)|k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3))=X2), inference(spm,[status(thm)],[c_0_53, c_0_46])).
% 0.20/0.42  cnf(c_0_61, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))=k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk5_0)), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.42  cnf(c_0_62, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.42  cnf(c_0_63, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_56])).
% 0.20/0.42  cnf(c_0_64, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.42  cnf(c_0_65, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.42  cnf(c_0_66, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,esk4_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))=k4_xboole_0(esk3_0,esk4_0)|k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk5_0)=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.42  cnf(c_0_67, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_62])).
% 0.20/0.42  cnf(c_0_68, negated_conjecture, (k4_xboole_0(esk4_0,esk5_0)=esk4_0), inference(spm,[status(thm)],[c_0_43, c_0_63])).
% 0.20/0.42  cnf(c_0_69, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_64, c_0_26])).
% 0.20/0.42  cnf(c_0_70, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk5_0)=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))|~r2_hidden(esk6_0,k4_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.42  cnf(c_0_71, plain, (k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))=X1|r2_hidden(X2,k4_xboole_0(X1,X3))|r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_67, c_0_46])).
% 0.20/0.42  cnf(c_0_72, negated_conjecture, (~r2_hidden(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_45, c_0_68])).
% 0.20/0.42  cnf(c_0_73, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))))), inference(spm,[status(thm)],[c_0_69, c_0_38])).
% 0.20/0.42  cnf(c_0_74, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_32, c_0_44])).
% 0.20/0.42  cnf(c_0_75, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk5_0)=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))|k4_xboole_0(esk3_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])).
% 0.20/0.42  fof(c_0_76, plain, ![X42, X43]:k3_tarski(k2_tarski(X42,X43))=k2_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.42  cnf(c_0_77, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_73, c_0_50])).
% 0.20/0.42  cnf(c_0_78, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk5_0)=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))|r1_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.42  cnf(c_0_79, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.42  fof(c_0_80, plain, ![X29, X30, X31]:((r1_xboole_0(X29,k2_xboole_0(X30,X31))|~r1_xboole_0(X29,X30)|~r1_xboole_0(X29,X31))&((r1_xboole_0(X29,X30)|~r1_xboole_0(X29,k2_xboole_0(X30,X31)))&(r1_xboole_0(X29,X31)|~r1_xboole_0(X29,k2_xboole_0(X30,X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.20/0.42  cnf(c_0_81, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.42  cnf(c_0_82, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk5_0))), inference(spm,[status(thm)],[c_0_77, c_0_55])).
% 0.20/0.42  cnf(c_0_83, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk5_0)=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))|k4_xboole_0(esk3_0,esk4_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_78]), c_0_50])).
% 0.20/0.42  cnf(c_0_84, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_79, c_0_26])).
% 0.20/0.42  cnf(c_0_85, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.42  cnf(c_0_86, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_81, c_0_24])).
% 0.20/0.42  cnf(c_0_87, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk3_0|~r2_hidden(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.20/0.42  cnf(c_0_88, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_43, c_0_84])).
% 0.20/0.42  cnf(c_0_89, plain, (r1_xboole_0(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3)))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86]), c_0_25])).
% 0.20/0.42  cnf(c_0_90, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk3_0), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.20/0.42  cnf(c_0_91, negated_conjecture, (r1_xboole_0(esk4_0,k3_tarski(k2_enumset1(X1,X1,X1,esk5_0)))|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_89, c_0_63])).
% 0.20/0.42  cnf(c_0_92, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_90])).
% 0.20/0.42  cnf(c_0_93, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_94, negated_conjecture, (r1_xboole_0(esk4_0,k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.20/0.42  cnf(c_0_95, negated_conjecture, (~r1_xboole_0(k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0)),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_86]), c_0_25])).
% 0.20/0.42  cnf(c_0_96, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_94]), c_0_95]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 97
% 0.20/0.42  # Proof object clause steps            : 66
% 0.20/0.42  # Proof object formula steps           : 31
% 0.20/0.42  # Proof object conjectures             : 34
% 0.20/0.42  # Proof object clause conjectures      : 31
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 21
% 0.20/0.42  # Proof object initial formulas used   : 15
% 0.20/0.42  # Proof object generating inferences   : 33
% 0.20/0.42  # Proof object simplifying inferences  : 24
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 15
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 28
% 0.20/0.42  # Removed in clause preprocessing      : 5
% 0.20/0.42  # Initial clauses in saturation        : 23
% 0.20/0.42  # Processed clauses                    : 631
% 0.20/0.42  # ...of these trivial                  : 63
% 0.20/0.42  # ...subsumed                          : 300
% 0.20/0.42  # ...remaining for further processing  : 268
% 0.20/0.42  # Other redundant clauses eliminated   : 3
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 3
% 0.20/0.42  # Backward-rewritten                   : 88
% 0.20/0.42  # Generated clauses                    : 2365
% 0.20/0.42  # ...of the previous two non-trivial   : 1740
% 0.20/0.42  # Contextual simplify-reflections      : 0
% 0.20/0.42  # Paramodulations                      : 2360
% 0.20/0.42  # Factorizations                       : 2
% 0.20/0.42  # Equation resolutions                 : 3
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 151
% 0.20/0.42  #    Positive orientable unit clauses  : 71
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 24
% 0.20/0.42  #    Non-unit-clauses                  : 56
% 0.20/0.42  # Current number of unprocessed clauses: 1134
% 0.20/0.42  # ...number of literals in the above   : 2147
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 119
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 537
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 512
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 82
% 0.20/0.42  # Unit Clause-clause subsumption calls : 200
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 110
% 0.20/0.42  # BW rewrite match successes           : 28
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 41840
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.066 s
% 0.20/0.42  # System time              : 0.007 s
% 0.20/0.42  # Total time               : 0.073 s
% 0.20/0.42  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
