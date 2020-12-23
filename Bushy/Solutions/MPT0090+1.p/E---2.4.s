%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t83_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:33 EDT 2019

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 931 expanded)
%              Number of clauses        :   43 ( 436 expanded)
%              Number of leaves         :    7 ( 217 expanded)
%              Depth                    :   15
%              Number of atoms          :  164 (4145 expanded)
%              Number of equality atoms :   42 (1185 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t83_xboole_1,conjecture,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t83_xboole_1.p',t83_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t83_xboole_1.p',d5_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t83_xboole_1.p',d4_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t83_xboole_1.p',t4_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t83_xboole_1.p',t2_boole)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t83_xboole_1.p',d7_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t83_xboole_1.p',commutativity_k3_xboole_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_xboole_0(X1,X2)
      <=> k4_xboole_0(X1,X2) = X1 ) ),
    inference(assume_negation,[status(cth)],[t83_xboole_1])).

fof(c_0_8,negated_conjecture,
    ( ( ~ r1_xboole_0(esk1_0,esk2_0)
      | k4_xboole_0(esk1_0,esk2_0) != esk1_0 )
    & ( r1_xboole_0(esk1_0,esk2_0)
      | k4_xboole_0(esk1_0,esk2_0) = esk1_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_9,plain,(
    ! [X28,X29,X30,X31,X32,X33,X34,X35] :
      ( ( r2_hidden(X31,X28)
        | ~ r2_hidden(X31,X30)
        | X30 != k4_xboole_0(X28,X29) )
      & ( ~ r2_hidden(X31,X29)
        | ~ r2_hidden(X31,X30)
        | X30 != k4_xboole_0(X28,X29) )
      & ( ~ r2_hidden(X32,X28)
        | r2_hidden(X32,X29)
        | r2_hidden(X32,X30)
        | X30 != k4_xboole_0(X28,X29) )
      & ( ~ r2_hidden(esk5_3(X33,X34,X35),X35)
        | ~ r2_hidden(esk5_3(X33,X34,X35),X33)
        | r2_hidden(esk5_3(X33,X34,X35),X34)
        | X35 = k4_xboole_0(X33,X34) )
      & ( r2_hidden(esk5_3(X33,X34,X35),X33)
        | r2_hidden(esk5_3(X33,X34,X35),X35)
        | X35 = k4_xboole_0(X33,X34) )
      & ( ~ r2_hidden(esk5_3(X33,X34,X35),X34)
        | r2_hidden(esk5_3(X33,X34,X35),X35)
        | X35 = k4_xboole_0(X33,X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_10,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26] :
      ( ( r2_hidden(X22,X19)
        | ~ r2_hidden(X22,X21)
        | X21 != k3_xboole_0(X19,X20) )
      & ( r2_hidden(X22,X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k3_xboole_0(X19,X20) )
      & ( ~ r2_hidden(X23,X19)
        | ~ r2_hidden(X23,X20)
        | r2_hidden(X23,X21)
        | X21 != k3_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk4_3(X24,X25,X26),X26)
        | ~ r2_hidden(esk4_3(X24,X25,X26),X24)
        | ~ r2_hidden(esk4_3(X24,X25,X26),X25)
        | X26 = k3_xboole_0(X24,X25) )
      & ( r2_hidden(esk4_3(X24,X25,X26),X24)
        | r2_hidden(esk4_3(X24,X25,X26),X26)
        | X26 = k3_xboole_0(X24,X25) )
      & ( r2_hidden(esk4_3(X24,X25,X26),X25)
        | r2_hidden(esk4_3(X24,X25,X26),X26)
        | X26 = k3_xboole_0(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_11,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0)
    | k4_xboole_0(esk1_0,esk2_0) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X45,X46,X48,X49,X50] :
      ( ( r1_xboole_0(X45,X46)
        | r2_hidden(esk6_2(X45,X46),k3_xboole_0(X45,X46)) )
      & ( ~ r2_hidden(X50,k3_xboole_0(X48,X49))
        | ~ r1_xboole_0(X48,X49) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk2_0,esk1_0),esk1_0)
    | ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12])])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk6_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0)
    | k4_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk6_2(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))
    | r2_hidden(esk5_3(esk1_0,esk2_0,esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X42] : k3_xboole_0(X42,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_25,plain,(
    ! [X37,X38] :
      ( ( ~ r1_xboole_0(X37,X38)
        | k3_xboole_0(X37,X38) = k1_xboole_0 )
      & ( k3_xboole_0(X37,X38) != k1_xboole_0
        | r1_xboole_0(X37,X38) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0)
    | ~ r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk2_0,esk1_0),esk1_0)
    | r2_hidden(esk6_2(esk1_0,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk2_0,esk1_0),esk1_0)
    | r2_hidden(esk6_2(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

fof(c_0_29,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk2_0,esk1_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_16])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = esk1_0
    | r2_hidden(esk5_3(esk1_0,esk2_0,esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_34])])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk2_0,esk1_0),esk2_0)
    | ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_38])).

cnf(c_0_43,plain,
    ( r2_hidden(esk4_3(X1,X2,k1_xboole_0),X2)
    | r1_xboole_0(X2,X1) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40])]),c_0_41])).

cnf(c_0_44,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X1)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk2_0,esk1_0),esk2_0)
    | ~ r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk4_3(esk2_0,esk1_0,k1_xboole_0),esk1_0)
    | r2_hidden(esk5_3(esk1_0,esk2_0,esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,plain,
    ( r2_hidden(esk4_3(X1,X2,k1_xboole_0),X1)
    | r1_xboole_0(X2,X1) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_44])]),c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk2_0,esk1_0),esk2_0)
    | ~ r2_hidden(esk4_3(esk2_0,esk1_0,k1_xboole_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0)
    | ~ r2_hidden(esk5_3(esk1_0,esk2_0,esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk2_0,esk1_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_47]),c_0_48])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk2_0,esk1_0),k3_xboole_0(X1,esk1_0))
    | ~ r2_hidden(esk5_3(esk1_0,esk2_0,esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_34])).

cnf(c_0_56,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_51]),c_0_35]),c_0_56]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
