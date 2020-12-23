%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0283+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:21 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 127 expanded)
%              Number of clauses        :   42 (  63 expanded)
%              Number of leaves         :   14 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  198 ( 362 expanded)
%              Number of equality atoms :   53 (  83 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t84_zfmisc_1,conjecture,(
    ! [X1,X2] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X1,X2)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_zfmisc_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_14,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X16,X15)
        | r1_tarski(X16,X14)
        | X15 != k1_zfmisc_1(X14) )
      & ( ~ r1_tarski(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k1_zfmisc_1(X14) )
      & ( ~ r2_hidden(esk2_2(X18,X19),X19)
        | ~ r1_tarski(esk2_2(X18,X19),X18)
        | X19 = k1_zfmisc_1(X18) )
      & ( r2_hidden(esk2_2(X18,X19),X19)
        | r1_tarski(esk2_2(X18,X19),X18)
        | X19 = k1_zfmisc_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X1,X2)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)))) ),
    inference(assume_negation,[status(cth)],[t84_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X47,X48,X49] :
      ( ~ r1_tarski(X47,X48)
      | ~ r1_tarski(X48,X49)
      | r1_tarski(X47,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,negated_conjecture,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(esk6_0,esk7_0)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk7_0)))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_19,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( ~ r1_tarski(X21,X22)
        | ~ r2_hidden(X23,X21)
        | r2_hidden(X23,X22) )
      & ( r2_hidden(esk3_2(X24,X25),X24)
        | r1_tarski(X24,X25) )
      & ( ~ r2_hidden(esk3_2(X24,X25),X25)
        | r1_tarski(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(esk6_0,esk7_0)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X52,X53] : r1_tarski(k4_xboole_0(X52,X53),X52) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_25,plain,(
    ! [X54] : k4_xboole_0(X54,k1_xboole_0) = X54 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_26,plain,(
    ! [X27,X28,X29,X30,X31,X32,X33,X34] :
      ( ( ~ r2_hidden(X30,X29)
        | r2_hidden(X30,X27)
        | r2_hidden(X30,X28)
        | X29 != k2_xboole_0(X27,X28) )
      & ( ~ r2_hidden(X31,X27)
        | r2_hidden(X31,X29)
        | X29 != k2_xboole_0(X27,X28) )
      & ( ~ r2_hidden(X31,X28)
        | r2_hidden(X31,X29)
        | X29 != k2_xboole_0(X27,X28) )
      & ( ~ r2_hidden(esk4_3(X32,X33,X34),X32)
        | ~ r2_hidden(esk4_3(X32,X33,X34),X34)
        | X34 = k2_xboole_0(X32,X33) )
      & ( ~ r2_hidden(esk4_3(X32,X33,X34),X33)
        | ~ r2_hidden(esk4_3(X32,X33,X34),X34)
        | X34 = k2_xboole_0(X32,X33) )
      & ( r2_hidden(esk4_3(X32,X33,X34),X34)
        | r2_hidden(esk4_3(X32,X33,X34),X32)
        | r2_hidden(esk4_3(X32,X33,X34),X33)
        | X34 = k2_xboole_0(X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r2_hidden(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk3_2(k1_zfmisc_1(k4_xboole_0(esk6_0,esk7_0)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk7_0)))),k1_zfmisc_1(k4_xboole_0(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42,X43] :
      ( ( r2_hidden(X39,X36)
        | ~ r2_hidden(X39,X38)
        | X38 != k4_xboole_0(X36,X37) )
      & ( ~ r2_hidden(X39,X37)
        | ~ r2_hidden(X39,X38)
        | X38 != k4_xboole_0(X36,X37) )
      & ( ~ r2_hidden(X40,X36)
        | r2_hidden(X40,X37)
        | r2_hidden(X40,X38)
        | X38 != k4_xboole_0(X36,X37) )
      & ( ~ r2_hidden(esk5_3(X41,X42,X43),X43)
        | ~ r2_hidden(esk5_3(X41,X42,X43),X41)
        | r2_hidden(esk5_3(X41,X42,X43),X42)
        | X43 = k4_xboole_0(X41,X42) )
      & ( r2_hidden(esk5_3(X41,X42,X43),X41)
        | r2_hidden(esk5_3(X41,X42,X43),X43)
        | X43 = k4_xboole_0(X41,X42) )
      & ( ~ r2_hidden(esk5_3(X41,X42,X43),X42)
        | r2_hidden(esk5_3(X41,X42,X43),X43)
        | X43 = k4_xboole_0(X41,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(X1,k4_xboole_0(esk6_0,esk7_0))
    | ~ r1_tarski(X1,esk3_2(k1_zfmisc_1(k4_xboole_0(esk6_0,esk7_0)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk7_0))))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_36,plain,(
    ! [X56,X57,X58] :
      ( ~ r1_tarski(X56,X57)
      | ~ r1_xboole_0(X57,X58)
      | r1_xboole_0(X56,X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_37,plain,(
    ! [X59,X60] : r1_xboole_0(k4_xboole_0(X59,X60),X60) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(esk3_2(k1_zfmisc_1(k4_xboole_0(esk6_0,esk7_0)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk7_0)))),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_31])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk3_2(k1_zfmisc_1(k4_xboole_0(esk6_0,esk7_0)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk7_0)))),k4_xboole_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_44,plain,(
    ! [X45,X46] :
      ( ( ~ r1_xboole_0(X45,X46)
        | k3_xboole_0(X45,X46) = k1_xboole_0 )
      & ( k3_xboole_0(X45,X46) != k1_xboole_0
        | r1_xboole_0(X45,X46) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_47,plain,(
    ! [X50,X51] :
      ( ~ r1_tarski(X50,X51)
      | k3_xboole_0(X50,X51) = X50 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(esk3_2(k1_zfmisc_1(k4_xboole_0(esk6_0,esk7_0)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk7_0)))),k4_xboole_0(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk3_2(k1_zfmisc_1(k4_xboole_0(esk6_0,esk7_0)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk7_0)))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_54,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_2(k1_zfmisc_1(k4_xboole_0(esk6_0,esk7_0)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk7_0)))),k1_zfmisc_1(esk7_0))
    | ~ r2_hidden(esk3_2(k1_zfmisc_1(k4_xboole_0(esk6_0,esk7_0)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk7_0)))),k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk3_2(k1_zfmisc_1(k4_xboole_0(esk6_0,esk7_0)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk7_0)))),k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_61,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X9,X8)
        | X9 = X7
        | X8 != k1_tarski(X7) )
      & ( X10 != X7
        | r2_hidden(X10,X8)
        | X8 != k1_tarski(X7) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | esk1_2(X11,X12) != X11
        | X12 = k1_tarski(X11) )
      & ( r2_hidden(esk1_2(X11,X12),X12)
        | esk1_2(X11,X12) = X11
        | X12 = k1_tarski(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_21])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_2(k1_zfmisc_1(k4_xboole_0(esk6_0,esk7_0)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk7_0)))),k1_zfmisc_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_65,negated_conjecture,
    ( k3_xboole_0(esk7_0,esk3_2(k1_zfmisc_1(k4_xboole_0(esk6_0,esk7_0)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk7_0))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_43]),c_0_60])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_hidden(esk3_2(k1_zfmisc_1(k4_xboole_0(esk6_0,esk7_0)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk7_0)))),k1_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( esk3_2(k1_zfmisc_1(k4_xboole_0(esk6_0,esk7_0)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk7_0)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_60]),c_0_65])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_66])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68]),c_0_69])]),
    [proof]).

%------------------------------------------------------------------------------
