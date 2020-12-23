%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t12_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:12 EDT 2019

% Result     : Theorem 0.50s
% Output     : CNFRefutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 313 expanded)
%              Number of clauses        :   35 ( 158 expanded)
%              Number of leaves         :    7 (  82 expanded)
%              Depth                    :   14
%              Number of atoms          :  176 (1340 expanded)
%              Number of equality atoms :   85 ( 651 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t12_setfam_1.p',d2_tarski)).

fof(t12_setfam_1,conjecture,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t12_setfam_1.p',t12_setfam_1)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t12_setfam_1.p',d1_setfam_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t12_setfam_1.p',d4_xboole_0)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t12_setfam_1.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t12_setfam_1.p',dt_o_0_0_xboole_0)).

fof(fc3_xboole_0,axiom,(
    ! [X1,X2] : ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t12_setfam_1.p',fc3_xboole_0)).

fof(c_0_7,plain,(
    ! [X26,X27,X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X29,X28)
        | X29 = X26
        | X29 = X27
        | X28 != k2_tarski(X26,X27) )
      & ( X30 != X26
        | r2_hidden(X30,X28)
        | X28 != k2_tarski(X26,X27) )
      & ( X30 != X27
        | r2_hidden(X30,X28)
        | X28 != k2_tarski(X26,X27) )
      & ( esk6_3(X31,X32,X33) != X31
        | ~ r2_hidden(esk6_3(X31,X32,X33),X33)
        | X33 = k2_tarski(X31,X32) )
      & ( esk6_3(X31,X32,X33) != X32
        | ~ r2_hidden(esk6_3(X31,X32,X33),X33)
        | X33 = k2_tarski(X31,X32) )
      & ( r2_hidden(esk6_3(X31,X32,X33),X33)
        | esk6_3(X31,X32,X33) = X31
        | esk6_3(X31,X32,X33) = X32
        | X33 = k2_tarski(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t12_setfam_1])).

fof(c_0_9,plain,(
    ! [X13,X14,X15,X16,X17,X19,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X15,X14)
        | ~ r2_hidden(X16,X13)
        | r2_hidden(X15,X16)
        | X14 != k1_setfam_1(X13)
        | X13 = k1_xboole_0 )
      & ( r2_hidden(esk3_3(X13,X14,X17),X13)
        | r2_hidden(X17,X14)
        | X14 != k1_setfam_1(X13)
        | X13 = k1_xboole_0 )
      & ( ~ r2_hidden(X17,esk3_3(X13,X14,X17))
        | r2_hidden(X17,X14)
        | X14 != k1_setfam_1(X13)
        | X13 = k1_xboole_0 )
      & ( r2_hidden(esk5_2(X13,X19),X13)
        | ~ r2_hidden(esk4_2(X13,X19),X19)
        | X19 = k1_setfam_1(X13)
        | X13 = k1_xboole_0 )
      & ( ~ r2_hidden(esk4_2(X13,X19),esk5_2(X13,X19))
        | ~ r2_hidden(esk4_2(X13,X19),X19)
        | X19 = k1_setfam_1(X13)
        | X13 = k1_xboole_0 )
      & ( r2_hidden(esk4_2(X13,X19),X19)
        | ~ r2_hidden(X22,X13)
        | r2_hidden(esk4_2(X13,X19),X22)
        | X19 = k1_setfam_1(X13)
        | X13 = k1_xboole_0 )
      & ( X24 != k1_setfam_1(X23)
        | X24 = k1_xboole_0
        | X23 != k1_xboole_0 )
      & ( X25 != k1_xboole_0
        | X25 = k1_setfam_1(X23)
        | X23 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41,X42] :
      ( ( r2_hidden(X38,X35)
        | ~ r2_hidden(X38,X37)
        | X37 != k3_xboole_0(X35,X36) )
      & ( r2_hidden(X38,X36)
        | ~ r2_hidden(X38,X37)
        | X37 != k3_xboole_0(X35,X36) )
      & ( ~ r2_hidden(X39,X35)
        | ~ r2_hidden(X39,X36)
        | r2_hidden(X39,X37)
        | X37 != k3_xboole_0(X35,X36) )
      & ( ~ r2_hidden(esk7_3(X40,X41,X42),X42)
        | ~ r2_hidden(esk7_3(X40,X41,X42),X40)
        | ~ r2_hidden(esk7_3(X40,X41,X42),X41)
        | X42 = k3_xboole_0(X40,X41) )
      & ( r2_hidden(esk7_3(X40,X41,X42),X40)
        | r2_hidden(esk7_3(X40,X41,X42),X42)
        | X42 = k3_xboole_0(X40,X41) )
      & ( r2_hidden(esk7_3(X40,X41,X42),X41)
        | r2_hidden(esk7_3(X40,X41,X42),X42)
        | X42 = k3_xboole_0(X40,X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_12,plain,(
    ! [X52] :
      ( ~ v1_xboole_0(X52)
      | X52 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_13,negated_conjecture,(
    k1_setfam_1(k2_tarski(esk1_0,esk2_0)) != k3_xboole_0(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_14,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r2_hidden(esk4_2(X1,X2),X3)
    | X2 = k1_setfam_1(X1)
    | X1 = k1_xboole_0
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_10])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_20,plain,(
    ! [X57,X58] : ~ v1_xboole_0(k2_tarski(X57,X58)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_xboole_0])])).

cnf(c_0_21,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk1_0,esk2_0)) != k3_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( X1 = k1_setfam_1(k2_tarski(X2,X3))
    | k2_tarski(X2,X3) = k1_xboole_0
    | r2_hidden(esk4_2(k2_tarski(X2,X3),X1),X1)
    | r2_hidden(esk4_2(k2_tarski(X2,X3),X1),X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_19])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) = k1_xboole_0
    | r2_hidden(esk4_2(k2_tarski(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)),esk2_0) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22])]),c_0_23])).

cnf(c_0_30,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_24])).

cnf(c_0_31,plain,
    ( X1 = k1_setfam_1(k2_tarski(X2,X3))
    | k2_tarski(X2,X3) = k1_xboole_0
    | r2_hidden(esk4_2(k2_tarski(X2,X3),X1),X1)
    | r2_hidden(esk4_2(k2_tarski(X2,X3),X1),X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk4_2(k2_tarski(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_35,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) = k1_xboole_0
    | r2_hidden(esk4_2(k2_tarski(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)),esk1_0) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_31])]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk4_2(k2_tarski(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(X1,esk2_0))
    | ~ r2_hidden(esk4_2(k2_tarski(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk4_2(k2_tarski(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_35]),c_0_30])])).

cnf(c_0_38,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | X2 = k1_setfam_1(X1)
    | X1 = k1_xboole_0
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk4_2(k2_tarski(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_41,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) = k1_xboole_0
    | r2_hidden(esk5_2(k2_tarski(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_21])).

cnf(c_0_42,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk5_2(k2_tarski(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_41]),c_0_30])])).

cnf(c_0_44,plain,
    ( X2 = k1_setfam_1(X1)
    | X1 = k1_xboole_0
    | ~ r2_hidden(esk4_2(X1,X2),esk5_2(X1,X2))
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_45,negated_conjecture,
    ( esk5_2(k2_tarski(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) = esk2_0
    | esk5_2(k2_tarski(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( esk5_2(k2_tarski(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) = esk1_0
    | k2_tarski(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_34]),c_0_39])]),c_0_21])).

cnf(c_0_47,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_46]),c_0_37]),c_0_39])]),c_0_21])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_47]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
