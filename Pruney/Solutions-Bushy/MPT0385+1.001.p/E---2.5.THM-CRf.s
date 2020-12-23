%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0385+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:32 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (2803 expanded)
%              Number of clauses        :   43 (1552 expanded)
%              Number of leaves         :    6 ( 624 expanded)
%              Depth                    :   20
%              Number of atoms          :  174 (14345 expanded)
%              Number of equality atoms :   54 (4311 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    9 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(t3_setfam_1,conjecture,(
    ! [X1] : r1_tarski(k1_setfam_1(X1),k3_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_setfam_1)).

fof(c_0_6,plain,(
    ! [X26,X27,X28,X30,X31,X32,X33,X35] :
      ( ( r2_hidden(X28,esk5_3(X26,X27,X28))
        | ~ r2_hidden(X28,X27)
        | X27 != k3_tarski(X26) )
      & ( r2_hidden(esk5_3(X26,X27,X28),X26)
        | ~ r2_hidden(X28,X27)
        | X27 != k3_tarski(X26) )
      & ( ~ r2_hidden(X30,X31)
        | ~ r2_hidden(X31,X26)
        | r2_hidden(X30,X27)
        | X27 != k3_tarski(X26) )
      & ( ~ r2_hidden(esk6_2(X32,X33),X33)
        | ~ r2_hidden(esk6_2(X32,X33),X35)
        | ~ r2_hidden(X35,X32)
        | X33 = k3_tarski(X32) )
      & ( r2_hidden(esk6_2(X32,X33),esk7_2(X32,X33))
        | r2_hidden(esk6_2(X32,X33),X33)
        | X33 = k3_tarski(X32) )
      & ( r2_hidden(esk7_2(X32,X33),X32)
        | r2_hidden(esk6_2(X32,X33),X33)
        | X33 = k3_tarski(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_7,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,esk5_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( ~ r1_tarski(X20,X21)
        | ~ r2_hidden(X22,X20)
        | r2_hidden(X22,X21) )
      & ( r2_hidden(esk4_2(X23,X24),X23)
        | r1_tarski(X23,X24) )
      & ( ~ r2_hidden(esk4_2(X23,X24),X24)
        | r1_tarski(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_10,plain,(
    ! [X37] : r1_tarski(k1_xboole_0,X37) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,esk5_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(esk5_3(X1,k3_tarski(X1),X2),X2)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk5_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( r2_hidden(esk5_3(k1_xboole_0,k3_tarski(k1_xboole_0),X1),X2)
    | ~ r2_hidden(X1,k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k3_tarski(k3_tarski(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k3_tarski(k3_tarski(k3_tarski(k1_xboole_0)))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17])).

fof(c_0_24,plain,(
    ! [X7,X8,X9,X10,X11,X13,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X9,X8)
        | ~ r2_hidden(X10,X7)
        | r2_hidden(X9,X10)
        | X8 != k1_setfam_1(X7)
        | X7 = k1_xboole_0 )
      & ( r2_hidden(esk1_3(X7,X8,X11),X7)
        | r2_hidden(X11,X8)
        | X8 != k1_setfam_1(X7)
        | X7 = k1_xboole_0 )
      & ( ~ r2_hidden(X11,esk1_3(X7,X8,X11))
        | r2_hidden(X11,X8)
        | X8 != k1_setfam_1(X7)
        | X7 = k1_xboole_0 )
      & ( r2_hidden(esk3_2(X7,X13),X7)
        | ~ r2_hidden(esk2_2(X7,X13),X13)
        | X13 = k1_setfam_1(X7)
        | X7 = k1_xboole_0 )
      & ( ~ r2_hidden(esk2_2(X7,X13),esk3_2(X7,X13))
        | ~ r2_hidden(esk2_2(X7,X13),X13)
        | X13 = k1_setfam_1(X7)
        | X7 = k1_xboole_0 )
      & ( r2_hidden(esk2_2(X7,X13),X13)
        | ~ r2_hidden(X16,X7)
        | r2_hidden(esk2_2(X7,X13),X16)
        | X13 = k1_setfam_1(X7)
        | X7 = k1_xboole_0 )
      & ( X18 != k1_setfam_1(X17)
        | X18 = k1_xboole_0
        | X17 != k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | X19 = k1_setfam_1(X17)
        | X17 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k1_xboole_0))))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_17])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k1_xboole_0)))))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_17])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(X1,k1_setfam_1(X1),X2),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k1_xboole_0))))))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_17])).

cnf(c_0_30,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0
    | r2_hidden(X1,k1_setfam_1(k3_tarski(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_28])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k1_xboole_0)))))))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_17])).

cnf(c_0_32,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0
    | ~ r2_hidden(k1_setfam_1(k3_tarski(k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_30])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k1_xboole_0))))))))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_17])).

cnf(c_0_34,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_30])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34])).

cnf(c_0_38,plain,
    ( r2_hidden(esk7_2(X1,X2),X1)
    | r2_hidden(esk6_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk6_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_34])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X1),X2)
    | r2_hidden(esk4_2(k1_setfam_1(X1),X2),X3)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_44,negated_conjecture,(
    ~ ! [X1] : r1_tarski(k1_setfam_1(X1),k3_tarski(X1)) ),
    inference(assume_negation,[status(cth)],[t3_setfam_1])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k3_tarski(X1))
    | ~ r2_hidden(X2,esk6_2(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X1),X2)
    | r2_hidden(esk4_2(k1_setfam_1(X1),X2),esk6_2(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_42])).

fof(c_0_47,negated_conjecture,(
    ~ r1_tarski(k1_setfam_1(esk8_0),k3_tarski(esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X1),X2)
    | r2_hidden(esk4_2(k1_setfam_1(X1),X2),k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(esk8_0),k3_tarski(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X1),k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | X1 != k1_setfam_1(X2)
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_53,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_53]),c_0_54]),c_0_53]),c_0_34]),c_0_15])]),
    [proof]).

%------------------------------------------------------------------------------
