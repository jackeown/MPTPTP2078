%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0385+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:32 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 100 expanded)
%              Number of clauses        :   21 (  47 expanded)
%              Number of leaves         :    8 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  142 ( 380 expanded)
%              Number of equality atoms :   46 ( 117 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(t3_setfam_1,conjecture,(
    ! [X1] : r1_tarski(k1_setfam_1(X1),k3_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_setfam_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_8,plain,(
    ! [X5,X6,X7,X8,X9,X11,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X7,X6)
        | ~ r2_hidden(X8,X5)
        | r2_hidden(X7,X8)
        | X6 != k1_setfam_1(X5)
        | X5 = k1_xboole_0 )
      & ( r2_hidden(esk1_3(X5,X6,X9),X5)
        | r2_hidden(X9,X6)
        | X6 != k1_setfam_1(X5)
        | X5 = k1_xboole_0 )
      & ( ~ r2_hidden(X9,esk1_3(X5,X6,X9))
        | r2_hidden(X9,X6)
        | X6 != k1_setfam_1(X5)
        | X5 = k1_xboole_0 )
      & ( r2_hidden(esk3_2(X5,X11),X5)
        | ~ r2_hidden(esk2_2(X5,X11),X11)
        | X11 = k1_setfam_1(X5)
        | X5 = k1_xboole_0 )
      & ( ~ r2_hidden(esk2_2(X5,X11),esk3_2(X5,X11))
        | ~ r2_hidden(esk2_2(X5,X11),X11)
        | X11 = k1_setfam_1(X5)
        | X5 = k1_xboole_0 )
      & ( r2_hidden(esk2_2(X5,X11),X11)
        | ~ r2_hidden(X14,X5)
        | r2_hidden(esk2_2(X5,X11),X14)
        | X11 = k1_setfam_1(X5)
        | X5 = k1_xboole_0 )
      & ( X16 != k1_setfam_1(X15)
        | X16 = k1_xboole_0
        | X15 != k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | X17 = k1_setfam_1(X15)
        | X15 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

fof(c_0_9,plain,(
    ! [X24,X25,X26,X28,X29,X30,X31,X33] :
      ( ( r2_hidden(X26,esk5_3(X24,X25,X26))
        | ~ r2_hidden(X26,X25)
        | X25 != k3_tarski(X24) )
      & ( r2_hidden(esk5_3(X24,X25,X26),X24)
        | ~ r2_hidden(X26,X25)
        | X25 != k3_tarski(X24) )
      & ( ~ r2_hidden(X28,X29)
        | ~ r2_hidden(X29,X24)
        | r2_hidden(X28,X25)
        | X25 != k3_tarski(X24) )
      & ( ~ r2_hidden(esk6_2(X30,X31),X31)
        | ~ r2_hidden(esk6_2(X30,X31),X33)
        | ~ r2_hidden(X33,X30)
        | X31 = k3_tarski(X30) )
      & ( r2_hidden(esk6_2(X30,X31),esk7_2(X30,X31))
        | r2_hidden(esk6_2(X30,X31),X31)
        | X31 = k3_tarski(X30) )
      & ( r2_hidden(esk7_2(X30,X31),X30)
        | r2_hidden(esk6_2(X30,X31),X31)
        | X31 = k3_tarski(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_10,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X37,X38)
      | v1_xboole_0(X38)
      | r2_hidden(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_11,plain,(
    ! [X35] : m1_subset_1(esk8_1(X35),X35) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( ~ r1_tarski(X18,X19)
        | ~ r2_hidden(X20,X18)
        | r2_hidden(X20,X19) )
      & ( r2_hidden(esk4_2(X21,X22),X21)
        | r1_tarski(X21,X22) )
      & ( ~ r2_hidden(esk4_2(X21,X22),X22)
        | r1_tarski(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk8_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X40] :
      ( ~ v1_xboole_0(X40)
      | X40 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk8_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X1),X2)
    | r2_hidden(esk4_2(k1_setfam_1(X1),X2),X3)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] : r1_tarski(k1_setfam_1(X1),k3_tarski(X1)) ),
    inference(assume_negation,[status(cth)],[t3_setfam_1])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(X2,k3_tarski(X1))
    | ~ r2_hidden(X2,esk8_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X1),X2)
    | r2_hidden(esk4_2(k1_setfam_1(X1),X2),esk8_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_21]),c_0_23])).

fof(c_0_27,negated_conjecture,(
    ~ r1_tarski(k1_setfam_1(esk9_0),k3_tarski(esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X1),X2)
    | r2_hidden(esk4_2(k1_setfam_1(X1),X2),k3_tarski(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(esk9_0),k3_tarski(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X1),k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | X1 != k1_setfam_1(X2)
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_33,plain,(
    ! [X39] : r1_tarski(k1_xboole_0,X39) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_34,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_34]),c_0_35]),c_0_34]),c_0_36])]),
    [proof]).

%------------------------------------------------------------------------------
