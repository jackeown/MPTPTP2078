%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t71_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:31 EDT 2019

% Result     : Theorem 1.22s
% Output     : CNFRefutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 305 expanded)
%              Number of clauses        :   42 ( 145 expanded)
%              Number of leaves         :   13 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :  165 ( 998 expanded)
%              Number of equality atoms :   52 ( 333 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t71_xboole_1.p',d3_xboole_0)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t71_xboole_1.p',t6_boole)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t71_xboole_1.p',t7_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t71_xboole_1.p',dt_o_0_0_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t71_xboole_1.p',t1_boole)).

fof(t71_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
        & r1_xboole_0(X1,X2)
        & r1_xboole_0(X3,X2) )
     => X1 = X3 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t71_xboole_1.p',t71_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t71_xboole_1.p',commutativity_k2_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t71_xboole_1.p',d4_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t71_xboole_1.p',d7_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t71_xboole_1.p',commutativity_k3_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t71_xboole_1.p',idempotence_k2_xboole_0)).

fof(c_0_11,plain,(
    ! [X22,X23,X24,X25,X26,X27,X28,X29] :
      ( ( ~ r2_hidden(X25,X24)
        | r2_hidden(X25,X22)
        | r2_hidden(X25,X23)
        | X24 != k2_xboole_0(X22,X23) )
      & ( ~ r2_hidden(X26,X22)
        | r2_hidden(X26,X24)
        | X24 != k2_xboole_0(X22,X23) )
      & ( ~ r2_hidden(X26,X23)
        | r2_hidden(X26,X24)
        | X24 != k2_xboole_0(X22,X23) )
      & ( ~ r2_hidden(esk5_3(X27,X28,X29),X27)
        | ~ r2_hidden(esk5_3(X27,X28,X29),X29)
        | X29 = k2_xboole_0(X27,X28) )
      & ( ~ r2_hidden(esk5_3(X27,X28,X29),X28)
        | ~ r2_hidden(esk5_3(X27,X28,X29),X29)
        | X29 = k2_xboole_0(X27,X28) )
      & ( r2_hidden(esk5_3(X27,X28,X29),X29)
        | r2_hidden(esk5_3(X27,X28,X29),X27)
        | r2_hidden(esk5_3(X27,X28,X29),X28)
        | X29 = k2_xboole_0(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_12,plain,(
    ! [X48] :
      ( ~ v1_xboole_0(X48)
      | X48 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_13,plain,(
    ! [X49,X50] :
      ( ~ r2_hidden(X49,X50)
      | ~ v1_xboole_0(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X46] : k2_xboole_0(X46,k1_xboole_0) = X46 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_20,plain,
    ( ~ epred1_0
  <=> ! [X1] : ~ v1_xboole_0(X1) ),
    introduced(definition)).

cnf(c_0_21,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X3,X2) )
       => X1 = X3 ) ),
    inference(assume_negation,[status(cth)],[t71_xboole_1])).

fof(c_0_23,plain,
    ( ~ epred2_0
  <=> ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    introduced(definition)).

cnf(c_0_24,plain,
    ( ~ v1_xboole_0(k2_xboole_0(X1,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( epred1_0
    | ~ v1_xboole_0(X1) ),
    inference(split_equiv,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_21])).

fof(c_0_28,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = k2_xboole_0(esk3_0,esk2_0)
    & r1_xboole_0(esk1_0,esk2_0)
    & r1_xboole_0(esk3_0,esk2_0)
    & esk1_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_29,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k2_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_30,plain,(
    ! [X31,X32,X33,X34,X35,X36,X37,X38] :
      ( ( r2_hidden(X34,X31)
        | ~ r2_hidden(X34,X33)
        | X33 != k3_xboole_0(X31,X32) )
      & ( r2_hidden(X34,X32)
        | ~ r2_hidden(X34,X33)
        | X33 != k3_xboole_0(X31,X32) )
      & ( ~ r2_hidden(X35,X31)
        | ~ r2_hidden(X35,X32)
        | r2_hidden(X35,X33)
        | X33 != k3_xboole_0(X31,X32) )
      & ( ~ r2_hidden(esk6_3(X36,X37,X38),X38)
        | ~ r2_hidden(esk6_3(X36,X37,X38),X36)
        | ~ r2_hidden(esk6_3(X36,X37,X38),X37)
        | X38 = k3_xboole_0(X36,X37) )
      & ( r2_hidden(esk6_3(X36,X37,X38),X36)
        | r2_hidden(esk6_3(X36,X37,X38),X38)
        | X38 = k3_xboole_0(X36,X37) )
      & ( r2_hidden(esk6_3(X36,X37,X38),X37)
        | r2_hidden(esk6_3(X36,X37,X38),X38)
        | X38 = k3_xboole_0(X36,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_31,plain,(
    ! [X40,X41] :
      ( ( ~ r1_xboole_0(X40,X41)
        | k3_xboole_0(X40,X41) = k1_xboole_0 )
      & ( k3_xboole_0(X40,X41) != k1_xboole_0
        | r1_xboole_0(X40,X41) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_32,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_33,plain,
    ( ~ epred2_0
    | ~ epred1_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_20]),c_0_23])).

cnf(c_0_34,plain,
    ( epred1_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = k2_xboole_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( esk1_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X3)
    | r2_hidden(esk5_3(X1,X2,X3),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_39,plain,(
    ! [X42] : k2_xboole_0(X42,X42) = X42 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( ~ epred2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_47,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = k2_xboole_0(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk5_3(X1,X2,esk3_0),esk3_0)
    | r2_hidden(esk5_3(X1,X2,esk3_0),X1)
    | r2_hidden(esk5_3(X1,X2,esk3_0),X2)
    | k2_xboole_0(X1,X2) != esk1_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_23]),c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk1_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_45]),c_0_43])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk2_0,esk1_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk1_0,esk3_0),esk1_0)
    | r2_hidden(esk5_3(esk1_0,esk1_0,esk3_0),esk3_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49])])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_53]),c_0_52])).

cnf(c_0_59,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk2_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk1_0,esk3_0),k2_xboole_0(esk2_0,esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_18])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(esk5_3(esk1_0,esk1_0,esk3_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_56]),c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( esk3_0 = k2_xboole_0(X1,X2)
    | r2_hidden(esk5_3(X1,X2,esk3_0),esk2_0)
    | ~ r2_hidden(esk5_3(X1,X2,esk3_0),k2_xboole_0(esk2_0,esk1_0))
    | ~ r2_hidden(esk5_3(X1,X2,esk3_0),X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_0,esk1_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_61]),c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_61]),c_0_49]),c_0_64])]),c_0_37]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
