%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:58 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 757 expanded)
%              Number of clauses        :   77 ( 351 expanded)
%              Number of leaves         :   15 ( 191 expanded)
%              Depth                    :   16
%              Number of atoms          :  224 (1725 expanded)
%              Number of equality atoms :  106 (1025 expanded)
%              Maximal formula depth    :   23 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X28,X29] :
      ( ~ r1_tarski(X28,X29)
      | k3_xboole_0(X28,X29) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_17,plain,(
    ! [X30,X31] : r1_tarski(X30,k2_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_18,plain,(
    ! [X52,X53,X54] :
      ( k2_zfmisc_1(k2_xboole_0(X52,X53),X54) = k2_xboole_0(k2_zfmisc_1(X52,X54),k2_zfmisc_1(X53,X54))
      & k2_zfmisc_1(X54,k2_xboole_0(X52,X53)) = k2_xboole_0(k2_zfmisc_1(X54,X52),k2_zfmisc_1(X54,X53)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

fof(c_0_19,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k2_zfmisc_1(esk10_0,esk11_0)
    & esk8_0 != k1_xboole_0
    & esk9_0 != k1_xboole_0
    & ( esk8_0 != esk10_0
      | esk9_0 != esk11_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_20,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k2_zfmisc_1(esk10_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X55,X56,X57,X58] : k2_zfmisc_1(k3_xboole_0(X55,X56),k3_xboole_0(X57,X58)) = k3_xboole_0(k2_zfmisc_1(X55,X57),k2_zfmisc_1(X56,X58)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,X1)) = k2_zfmisc_1(esk10_0,k2_xboole_0(X1,esk11_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_30,plain,(
    ! [X22,X23] :
      ( ( r1_tarski(X22,X23)
        | X22 != X23 )
      & ( r1_tarski(X23,X22)
        | X22 != X23 )
      & ( ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X22)
        | X22 = X23 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_31,plain,(
    ! [X49,X50,X51] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X50,X49),k2_zfmisc_1(X51,X49))
        | X49 = k1_xboole_0
        | r1_tarski(X50,X51) )
      & ( ~ r1_tarski(k2_zfmisc_1(X49,X50),k2_zfmisc_1(X49,X51))
        | X49 = k1_xboole_0
        | r1_tarski(X50,X51) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_32,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,k2_xboole_0(X1,esk11_0))) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k2_xboole_0(X2,X4))) = k2_zfmisc_1(k3_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_35,plain,(
    ! [X11,X12] :
      ( ( ~ r1_xboole_0(X11,X12)
        | k3_xboole_0(X11,X12) = k1_xboole_0 )
      & ( k3_xboole_0(X11,X12) != k1_xboole_0
        | r1_xboole_0(X11,X12) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_36,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | k2_xboole_0(X24,X25) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_37,plain,(
    ! [X26,X27] : r1_tarski(k3_xboole_0(X26,X27),X26) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_38,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk8_0,esk10_0),esk9_0) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(X1,k3_xboole_0(esk8_0,esk10_0))
    | ~ r1_tarski(k2_zfmisc_1(X1,esk9_0),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

fof(c_0_47,plain,(
    ! [X32,X33,X34,X35,X38,X39,X40,X41,X42,X43,X45,X46] :
      ( ( r2_hidden(esk3_4(X32,X33,X34,X35),X32)
        | ~ r2_hidden(X35,X34)
        | X34 != k2_zfmisc_1(X32,X33) )
      & ( r2_hidden(esk4_4(X32,X33,X34,X35),X33)
        | ~ r2_hidden(X35,X34)
        | X34 != k2_zfmisc_1(X32,X33) )
      & ( X35 = k4_tarski(esk3_4(X32,X33,X34,X35),esk4_4(X32,X33,X34,X35))
        | ~ r2_hidden(X35,X34)
        | X34 != k2_zfmisc_1(X32,X33) )
      & ( ~ r2_hidden(X39,X32)
        | ~ r2_hidden(X40,X33)
        | X38 != k4_tarski(X39,X40)
        | r2_hidden(X38,X34)
        | X34 != k2_zfmisc_1(X32,X33) )
      & ( ~ r2_hidden(esk5_3(X41,X42,X43),X43)
        | ~ r2_hidden(X45,X41)
        | ~ r2_hidden(X46,X42)
        | esk5_3(X41,X42,X43) != k4_tarski(X45,X46)
        | X43 = k2_zfmisc_1(X41,X42) )
      & ( r2_hidden(esk6_3(X41,X42,X43),X41)
        | r2_hidden(esk5_3(X41,X42,X43),X43)
        | X43 = k2_zfmisc_1(X41,X42) )
      & ( r2_hidden(esk7_3(X41,X42,X43),X42)
        | r2_hidden(esk5_3(X41,X42,X43),X43)
        | X43 = k2_zfmisc_1(X41,X42) )
      & ( esk5_3(X41,X42,X43) = k4_tarski(esk6_3(X41,X42,X43),esk7_3(X41,X42,X43))
        | r2_hidden(esk5_3(X41,X42,X43),X43)
        | X43 = k2_zfmisc_1(X41,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_48,plain,(
    ! [X20] :
      ( X20 = k1_xboole_0
      | r2_hidden(esk2_1(X20),X20) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_21,c_0_41])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( r1_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_27])])).

fof(c_0_52,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r1_xboole_0(X14,X15)
        | r2_hidden(esk1_2(X14,X15),k3_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X19,k3_xboole_0(X17,X18))
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_25])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk8_0,k3_xboole_0(esk8_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_41])).

cnf(c_0_55,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) = k2_zfmisc_1(k3_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_49])).

cnf(c_0_59,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_50]),c_0_29])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_61,plain,
    ( r1_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_25])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_49])])).

cnf(c_0_64,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_65,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_53,c_0_50])).

cnf(c_0_66,negated_conjecture,
    ( k3_xboole_0(esk8_0,esk10_0) = esk8_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_54]),c_0_53])).

cnf(c_0_67,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_68,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_55])])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk2_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_70,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(X1,esk9_0),k2_zfmisc_1(esk8_0,esk11_0)) = k2_zfmisc_1(k3_xboole_0(X1,esk10_0),esk11_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_24]),c_0_59])).

cnf(c_0_71,plain,
    ( k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_72,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_49])).

cnf(c_0_74,negated_conjecture,
    ( k2_zfmisc_1(k2_xboole_0(esk8_0,esk10_0),esk9_0) = k2_zfmisc_1(esk10_0,k2_xboole_0(esk9_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_28])).

cnf(c_0_75,negated_conjecture,
    ( k2_xboole_0(esk8_0,esk10_0) = esk10_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_25])).

cnf(c_0_76,plain,
    ( r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( k2_zfmisc_1(esk10_0,k1_xboole_0) = k2_zfmisc_1(esk8_0,esk9_0)
    | r2_hidden(esk2_1(esk11_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_57])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_1(esk8_0),X1),k2_zfmisc_1(esk8_0,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk2_1(esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_57])).

cnf(c_0_80,negated_conjecture,
    ( k2_zfmisc_1(k2_xboole_0(esk8_0,k3_xboole_0(X1,esk10_0)),esk11_0) = k2_zfmisc_1(esk8_0,esk11_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_70]),c_0_64])).

cnf(c_0_81,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | r2_hidden(esk6_3(X1,X2,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_71]),c_0_71]),c_0_71]),c_0_73])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,k2_xboole_0(X1,esk11_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_28])).

cnf(c_0_84,negated_conjecture,
    ( k2_zfmisc_1(esk10_0,k2_xboole_0(esk9_0,esk11_0)) = k2_zfmisc_1(esk10_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk2_1(esk11_0),esk11_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_73])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_1(esk8_0),esk2_1(esk9_0)),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | r1_tarski(esk10_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(X1,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_24])).

cnf(c_0_88,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk11_0) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_49]),c_0_75]),c_0_24])).

cnf(c_0_89,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | r2_hidden(esk6_3(esk10_0,esk11_0,k1_xboole_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r1_tarski(esk11_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,X1)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_24])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk2_1(esk11_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | r1_tarski(esk10_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_41])])).

cnf(c_0_94,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_50])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk6_3(esk10_0,esk11_0,k1_xboole_0),esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_89]),c_0_73])).

cnf(c_0_96,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r1_tarski(esk11_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_97,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(esk10_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_73])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(esk8_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_66])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(esk11_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_73])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(X1,esk11_0)
    | ~ r1_tarski(k2_zfmisc_1(esk8_0,X1),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_88]),c_0_56])).

cnf(c_0_102,negated_conjecture,
    ( esk8_0 != esk10_0
    | esk9_0 != esk11_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_103,negated_conjecture,
    ( esk10_0 = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])])).

cnf(c_0_104,negated_conjecture,
    ( esk11_0 = esk9_0
    | ~ r1_tarski(esk9_0,esk11_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(esk9_0,esk11_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_41])).

cnf(c_0_106,negated_conjecture,
    ( esk11_0 != esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103])])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_105])]),c_0_106]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:58:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.39/0.55  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.39/0.55  # and selection function SelectNegativeLiterals.
% 0.39/0.55  #
% 0.39/0.55  # Preprocessing time       : 0.028 s
% 0.39/0.55  # Presaturation interreduction done
% 0.39/0.55  
% 0.39/0.55  # Proof found!
% 0.39/0.55  # SZS status Theorem
% 0.39/0.55  # SZS output start CNFRefutation
% 0.39/0.55  fof(t134_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.39/0.55  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.39/0.55  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.39/0.55  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 0.39/0.55  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.39/0.55  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.39/0.55  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.39/0.55  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 0.39/0.55  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.39/0.55  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.39/0.55  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.39/0.55  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.39/0.55  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.39/0.55  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.39/0.55  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.39/0.55  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4)))), inference(assume_negation,[status(cth)],[t134_zfmisc_1])).
% 0.39/0.55  fof(c_0_16, plain, ![X28, X29]:(~r1_tarski(X28,X29)|k3_xboole_0(X28,X29)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.39/0.55  fof(c_0_17, plain, ![X30, X31]:r1_tarski(X30,k2_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.39/0.55  fof(c_0_18, plain, ![X52, X53, X54]:(k2_zfmisc_1(k2_xboole_0(X52,X53),X54)=k2_xboole_0(k2_zfmisc_1(X52,X54),k2_zfmisc_1(X53,X54))&k2_zfmisc_1(X54,k2_xboole_0(X52,X53))=k2_xboole_0(k2_zfmisc_1(X54,X52),k2_zfmisc_1(X54,X53))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 0.39/0.55  fof(c_0_19, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k2_zfmisc_1(esk10_0,esk11_0)&((esk8_0!=k1_xboole_0&esk9_0!=k1_xboole_0)&(esk8_0!=esk10_0|esk9_0!=esk11_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.39/0.55  fof(c_0_20, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k2_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.39/0.55  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.39/0.55  cnf(c_0_22, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.55  cnf(c_0_23, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.55  cnf(c_0_24, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k2_zfmisc_1(esk10_0,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.55  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.39/0.55  fof(c_0_26, plain, ![X55, X56, X57, X58]:k2_zfmisc_1(k3_xboole_0(X55,X56),k3_xboole_0(X57,X58))=k3_xboole_0(k2_zfmisc_1(X55,X57),k2_zfmisc_1(X56,X58)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.39/0.55  cnf(c_0_27, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.39/0.55  cnf(c_0_28, negated_conjecture, (k2_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,X1))=k2_zfmisc_1(esk10_0,k2_xboole_0(X1,esk11_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.39/0.55  cnf(c_0_29, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.55  fof(c_0_30, plain, ![X22, X23]:(((r1_tarski(X22,X23)|X22!=X23)&(r1_tarski(X23,X22)|X22!=X23))&(~r1_tarski(X22,X23)|~r1_tarski(X23,X22)|X22=X23)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.39/0.55  fof(c_0_31, plain, ![X49, X50, X51]:((~r1_tarski(k2_zfmisc_1(X50,X49),k2_zfmisc_1(X51,X49))|X49=k1_xboole_0|r1_tarski(X50,X51))&(~r1_tarski(k2_zfmisc_1(X49,X50),k2_zfmisc_1(X49,X51))|X49=k1_xboole_0|r1_tarski(X50,X51))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 0.39/0.55  cnf(c_0_32, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,k2_xboole_0(X1,esk11_0)))=k2_zfmisc_1(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.39/0.55  cnf(c_0_33, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k2_xboole_0(X2,X4)))=k2_zfmisc_1(k3_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_29, c_0_27])).
% 0.39/0.55  cnf(c_0_34, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.39/0.55  fof(c_0_35, plain, ![X11, X12]:((~r1_xboole_0(X11,X12)|k3_xboole_0(X11,X12)=k1_xboole_0)&(k3_xboole_0(X11,X12)!=k1_xboole_0|r1_xboole_0(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.39/0.55  fof(c_0_36, plain, ![X24, X25]:(~r1_tarski(X24,X25)|k2_xboole_0(X24,X25)=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.39/0.55  fof(c_0_37, plain, ![X26, X27]:r1_tarski(k3_xboole_0(X26,X27),X26), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.39/0.55  cnf(c_0_38, plain, (X2=k1_xboole_0|r1_tarski(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.39/0.55  cnf(c_0_39, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk8_0,esk10_0),esk9_0)=k2_zfmisc_1(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.39/0.55  cnf(c_0_40, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.55  cnf(c_0_41, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_34])).
% 0.39/0.55  fof(c_0_42, plain, ![X9, X10]:k3_xboole_0(X9,X10)=k3_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.39/0.55  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.39/0.55  cnf(c_0_44, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.39/0.55  cnf(c_0_45, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.39/0.55  cnf(c_0_46, negated_conjecture, (r1_tarski(X1,k3_xboole_0(esk8_0,esk10_0))|~r1_tarski(k2_zfmisc_1(X1,esk9_0),k2_zfmisc_1(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.39/0.55  fof(c_0_47, plain, ![X32, X33, X34, X35, X38, X39, X40, X41, X42, X43, X45, X46]:(((((r2_hidden(esk3_4(X32,X33,X34,X35),X32)|~r2_hidden(X35,X34)|X34!=k2_zfmisc_1(X32,X33))&(r2_hidden(esk4_4(X32,X33,X34,X35),X33)|~r2_hidden(X35,X34)|X34!=k2_zfmisc_1(X32,X33)))&(X35=k4_tarski(esk3_4(X32,X33,X34,X35),esk4_4(X32,X33,X34,X35))|~r2_hidden(X35,X34)|X34!=k2_zfmisc_1(X32,X33)))&(~r2_hidden(X39,X32)|~r2_hidden(X40,X33)|X38!=k4_tarski(X39,X40)|r2_hidden(X38,X34)|X34!=k2_zfmisc_1(X32,X33)))&((~r2_hidden(esk5_3(X41,X42,X43),X43)|(~r2_hidden(X45,X41)|~r2_hidden(X46,X42)|esk5_3(X41,X42,X43)!=k4_tarski(X45,X46))|X43=k2_zfmisc_1(X41,X42))&(((r2_hidden(esk6_3(X41,X42,X43),X41)|r2_hidden(esk5_3(X41,X42,X43),X43)|X43=k2_zfmisc_1(X41,X42))&(r2_hidden(esk7_3(X41,X42,X43),X42)|r2_hidden(esk5_3(X41,X42,X43),X43)|X43=k2_zfmisc_1(X41,X42)))&(esk5_3(X41,X42,X43)=k4_tarski(esk6_3(X41,X42,X43),esk7_3(X41,X42,X43))|r2_hidden(esk5_3(X41,X42,X43),X43)|X43=k2_zfmisc_1(X41,X42))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.39/0.55  fof(c_0_48, plain, ![X20]:(X20=k1_xboole_0|r2_hidden(esk2_1(X20),X20)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.39/0.55  cnf(c_0_49, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_21, c_0_41])).
% 0.39/0.55  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.39/0.55  cnf(c_0_51, plain, (r1_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X1))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_27])])).
% 0.39/0.55  fof(c_0_52, plain, ![X14, X15, X17, X18, X19]:((r1_xboole_0(X14,X15)|r2_hidden(esk1_2(X14,X15),k3_xboole_0(X14,X15)))&(~r2_hidden(X19,k3_xboole_0(X17,X18))|~r1_xboole_0(X17,X18))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.39/0.55  cnf(c_0_53, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_25])).
% 0.39/0.55  cnf(c_0_54, negated_conjecture, (r1_tarski(esk8_0,k3_xboole_0(esk8_0,esk10_0))), inference(spm,[status(thm)],[c_0_46, c_0_41])).
% 0.39/0.55  cnf(c_0_55, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.39/0.55  cnf(c_0_56, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.55  cnf(c_0_57, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.39/0.55  cnf(c_0_58, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))=k2_zfmisc_1(k3_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_29, c_0_49])).
% 0.39/0.55  cnf(c_0_59, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X3,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_50]), c_0_29])).
% 0.39/0.55  cnf(c_0_60, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.39/0.55  cnf(c_0_61, plain, (r1_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_51, c_0_25])).
% 0.39/0.55  cnf(c_0_62, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.39/0.55  cnf(c_0_63, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_49])])).
% 0.39/0.55  cnf(c_0_64, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.55  cnf(c_0_65, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_53, c_0_50])).
% 0.39/0.55  cnf(c_0_66, negated_conjecture, (k3_xboole_0(esk8_0,esk10_0)=esk8_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_54]), c_0_53])).
% 0.39/0.55  cnf(c_0_67, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.39/0.55  cnf(c_0_68, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_55])])).
% 0.39/0.55  cnf(c_0_69, negated_conjecture, (r2_hidden(esk2_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.39/0.55  cnf(c_0_70, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(X1,esk9_0),k2_zfmisc_1(esk8_0,esk11_0))=k2_zfmisc_1(k3_xboole_0(X1,esk10_0),esk11_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_24]), c_0_59])).
% 0.39/0.55  cnf(c_0_71, plain, (k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.39/0.55  cnf(c_0_72, plain, (r2_hidden(esk6_3(X1,X2,X3),X1)|r2_hidden(esk5_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.39/0.55  cnf(c_0_73, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_49])).
% 0.39/0.55  cnf(c_0_74, negated_conjecture, (k2_zfmisc_1(k2_xboole_0(esk8_0,esk10_0),esk9_0)=k2_zfmisc_1(esk10_0,k2_xboole_0(esk9_0,esk11_0))), inference(spm,[status(thm)],[c_0_64, c_0_28])).
% 0.39/0.55  cnf(c_0_75, negated_conjecture, (k2_xboole_0(esk8_0,esk10_0)=esk10_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_25])).
% 0.39/0.55  cnf(c_0_76, plain, (r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_67])).
% 0.39/0.55  cnf(c_0_77, negated_conjecture, (k2_zfmisc_1(esk10_0,k1_xboole_0)=k2_zfmisc_1(esk8_0,esk9_0)|r2_hidden(esk2_1(esk11_0),esk11_0)), inference(spm,[status(thm)],[c_0_24, c_0_57])).
% 0.39/0.55  cnf(c_0_78, negated_conjecture, (r2_hidden(k4_tarski(esk2_1(esk8_0),X1),k2_zfmisc_1(esk8_0,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.39/0.55  cnf(c_0_79, negated_conjecture, (r2_hidden(esk2_1(esk9_0),esk9_0)), inference(spm,[status(thm)],[c_0_40, c_0_57])).
% 0.39/0.55  cnf(c_0_80, negated_conjecture, (k2_zfmisc_1(k2_xboole_0(esk8_0,k3_xboole_0(X1,esk10_0)),esk11_0)=k2_zfmisc_1(esk8_0,esk11_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_70]), c_0_64])).
% 0.39/0.55  cnf(c_0_81, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|r2_hidden(esk6_3(X1,X2,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_71]), c_0_71]), c_0_71]), c_0_73])).
% 0.39/0.55  cnf(c_0_82, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.39/0.55  cnf(c_0_83, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,k2_xboole_0(X1,esk11_0)))), inference(spm,[status(thm)],[c_0_22, c_0_28])).
% 0.39/0.55  cnf(c_0_84, negated_conjecture, (k2_zfmisc_1(esk10_0,k2_xboole_0(esk9_0,esk11_0))=k2_zfmisc_1(esk10_0,esk9_0)), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 0.39/0.55  cnf(c_0_85, negated_conjecture, (r2_hidden(esk2_1(esk11_0),esk11_0)|~r2_hidden(X1,k2_zfmisc_1(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_73])).
% 0.39/0.55  cnf(c_0_86, negated_conjecture, (r2_hidden(k4_tarski(esk2_1(esk8_0),esk2_1(esk9_0)),k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.39/0.55  cnf(c_0_87, negated_conjecture, (esk11_0=k1_xboole_0|r1_tarski(esk10_0,X1)|~r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(X1,esk11_0))), inference(spm,[status(thm)],[c_0_38, c_0_24])).
% 0.39/0.55  cnf(c_0_88, negated_conjecture, (k2_zfmisc_1(esk8_0,esk11_0)=k2_zfmisc_1(esk8_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_49]), c_0_75]), c_0_24])).
% 0.39/0.55  cnf(c_0_89, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|r2_hidden(esk6_3(esk10_0,esk11_0,k1_xboole_0),esk10_0)), inference(spm,[status(thm)],[c_0_24, c_0_81])).
% 0.39/0.55  cnf(c_0_90, negated_conjecture, (esk10_0=k1_xboole_0|r1_tarski(esk11_0,X1)|~r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,X1))), inference(spm,[status(thm)],[c_0_82, c_0_24])).
% 0.39/0.55  cnf(c_0_91, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk9_0))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.39/0.55  cnf(c_0_92, negated_conjecture, (r2_hidden(esk2_1(esk11_0),esk11_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.39/0.55  cnf(c_0_93, negated_conjecture, (esk11_0=k1_xboole_0|r1_tarski(esk10_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_41])])).
% 0.39/0.55  cnf(c_0_94, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_45, c_0_50])).
% 0.39/0.55  cnf(c_0_95, negated_conjecture, (r2_hidden(esk6_3(esk10_0,esk11_0,k1_xboole_0),esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_89]), c_0_73])).
% 0.39/0.55  cnf(c_0_96, negated_conjecture, (esk10_0=k1_xboole_0|r1_tarski(esk11_0,esk9_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.39/0.55  cnf(c_0_97, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.39/0.55  cnf(c_0_98, negated_conjecture, (r1_tarski(esk10_0,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_73])).
% 0.39/0.55  cnf(c_0_99, negated_conjecture, (r1_tarski(esk8_0,esk10_0)), inference(spm,[status(thm)],[c_0_94, c_0_66])).
% 0.39/0.55  cnf(c_0_100, negated_conjecture, (r1_tarski(esk11_0,esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_73])).
% 0.39/0.55  cnf(c_0_101, negated_conjecture, (r1_tarski(X1,esk11_0)|~r1_tarski(k2_zfmisc_1(esk8_0,X1),k2_zfmisc_1(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_88]), c_0_56])).
% 0.39/0.55  cnf(c_0_102, negated_conjecture, (esk8_0!=esk10_0|esk9_0!=esk11_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.55  cnf(c_0_103, negated_conjecture, (esk10_0=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])])).
% 0.39/0.55  cnf(c_0_104, negated_conjecture, (esk11_0=esk9_0|~r1_tarski(esk9_0,esk11_0)), inference(spm,[status(thm)],[c_0_97, c_0_100])).
% 0.39/0.55  cnf(c_0_105, negated_conjecture, (r1_tarski(esk9_0,esk11_0)), inference(spm,[status(thm)],[c_0_101, c_0_41])).
% 0.39/0.55  cnf(c_0_106, negated_conjecture, (esk11_0!=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_103])])).
% 0.39/0.55  cnf(c_0_107, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_105])]), c_0_106]), ['proof']).
% 0.39/0.55  # SZS output end CNFRefutation
% 0.39/0.55  # Proof object total steps             : 108
% 0.39/0.55  # Proof object clause steps            : 77
% 0.39/0.55  # Proof object formula steps           : 31
% 0.39/0.55  # Proof object conjectures             : 43
% 0.39/0.55  # Proof object clause conjectures      : 40
% 0.39/0.55  # Proof object formula conjectures     : 3
% 0.39/0.55  # Proof object initial clauses used    : 24
% 0.39/0.55  # Proof object initial formulas used   : 15
% 0.39/0.55  # Proof object generating inferences   : 47
% 0.39/0.55  # Proof object simplifying inferences  : 36
% 0.39/0.55  # Training examples: 0 positive, 0 negative
% 0.39/0.55  # Parsed axioms                        : 16
% 0.39/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.55  # Initial clauses                      : 32
% 0.39/0.55  # Removed in clause preprocessing      : 0
% 0.39/0.55  # Initial clauses in saturation        : 32
% 0.39/0.55  # Processed clauses                    : 1111
% 0.39/0.55  # ...of these trivial                  : 183
% 0.39/0.55  # ...subsumed                          : 424
% 0.39/0.55  # ...remaining for further processing  : 504
% 0.39/0.55  # Other redundant clauses eliminated   : 131
% 0.39/0.55  # Clauses deleted for lack of memory   : 0
% 0.39/0.55  # Backward-subsumed                    : 8
% 0.39/0.55  # Backward-rewritten                   : 194
% 0.39/0.55  # Generated clauses                    : 25917
% 0.39/0.55  # ...of the previous two non-trivial   : 18340
% 0.39/0.55  # Contextual simplify-reflections      : 0
% 0.39/0.55  # Paramodulations                      : 25787
% 0.39/0.55  # Factorizations                       : 0
% 0.39/0.55  # Equation resolutions                 : 131
% 0.39/0.55  # Propositional unsat checks           : 0
% 0.39/0.55  #    Propositional check models        : 0
% 0.39/0.55  #    Propositional check unsatisfiable : 0
% 0.39/0.55  #    Propositional clauses             : 0
% 0.39/0.55  #    Propositional clauses after purity: 0
% 0.39/0.55  #    Propositional unsat core size     : 0
% 0.39/0.55  #    Propositional preprocessing time  : 0.000
% 0.39/0.55  #    Propositional encoding time       : 0.000
% 0.39/0.55  #    Propositional solver time         : 0.000
% 0.39/0.55  #    Success case prop preproc time    : 0.000
% 0.39/0.55  #    Success case prop encoding time   : 0.000
% 0.39/0.55  #    Success case prop solver time     : 0.000
% 0.39/0.55  # Current number of processed clauses  : 265
% 0.39/0.55  #    Positive orientable unit clauses  : 118
% 0.39/0.55  #    Positive unorientable unit clauses: 3
% 0.39/0.55  #    Negative unit clauses             : 4
% 0.39/0.55  #    Non-unit-clauses                  : 140
% 0.39/0.55  # Current number of unprocessed clauses: 17034
% 0.39/0.55  # ...number of literals in the above   : 35286
% 0.39/0.55  # Current number of archived formulas  : 0
% 0.39/0.55  # Current number of archived clauses   : 233
% 0.39/0.55  # Clause-clause subsumption calls (NU) : 5589
% 0.39/0.55  # Rec. Clause-clause subsumption calls : 5084
% 0.39/0.55  # Non-unit clause-clause subsumptions  : 371
% 0.39/0.55  # Unit Clause-clause subsumption calls : 1150
% 0.39/0.55  # Rewrite failures with RHS unbound    : 0
% 0.39/0.55  # BW rewrite match attempts            : 150
% 0.39/0.55  # BW rewrite match successes           : 76
% 0.39/0.55  # Condensation attempts                : 0
% 0.39/0.55  # Condensation successes               : 0
% 0.39/0.55  # Termbank termtop insertions          : 358788
% 0.39/0.55  
% 0.39/0.55  # -------------------------------------------------
% 0.39/0.55  # User time                : 0.201 s
% 0.39/0.55  # System time              : 0.012 s
% 0.39/0.55  # Total time               : 0.214 s
% 0.39/0.55  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
