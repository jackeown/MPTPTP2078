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
% DateTime   : Thu Dec  3 10:43:24 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :  101 (4470 expanded)
%              Number of clauses        :   82 (2337 expanded)
%              Number of leaves         :    9 (1038 expanded)
%              Depth                    :   20
%              Number of atoms          :  284 (19083 expanded)
%              Number of equality atoms :   82 (4115 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t108_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ! [X5,X6] :
          ( r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X1,X2))
        <=> r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X3,X4)) )
     => k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_zfmisc_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(t103_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & r2_hidden(X4,X1)
        & ! [X5,X6] :
            ~ ( r2_hidden(X5,X2)
              & r2_hidden(X6,X3)
              & X4 = k4_tarski(X5,X6) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_9,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k4_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_11,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ! [X5,X6] :
            ( r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X1,X2))
          <=> r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X3,X4)) )
       => k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4) ) ),
    inference(assume_negation,[status(cth)],[t108_zfmisc_1])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X28] :
      ( ~ r1_tarski(X28,k1_xboole_0)
      | X28 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_20,plain,(
    ! [X29,X30,X31,X32] :
      ( ( r2_hidden(X29,X31)
        | ~ r2_hidden(k4_tarski(X29,X30),k2_zfmisc_1(X31,X32)) )
      & ( r2_hidden(X30,X32)
        | ~ r2_hidden(k4_tarski(X29,X30),k2_zfmisc_1(X31,X32)) )
      & ( ~ r2_hidden(X29,X31)
        | ~ r2_hidden(X30,X32)
        | r2_hidden(k4_tarski(X29,X30),k2_zfmisc_1(X31,X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_21,negated_conjecture,(
    ! [X43,X44] :
      ( ( ~ r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(esk6_0,esk7_0))
        | r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(esk8_0,esk9_0)) )
      & ( ~ r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(esk8_0,esk9_0))
        | r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(esk6_0,esk7_0)) )
      & k2_zfmisc_1(esk6_0,esk7_0) != k2_zfmisc_1(esk8_0,esk9_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).

cnf(c_0_22,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk8_0,esk9_0))
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk6_0,esk7_0))
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk6_0,esk7_0))
    | ~ r2_hidden(X2,esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_29])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_30])).

fof(c_0_36,plain,(
    ! [X22,X23] :
      ( ( ~ r2_hidden(esk3_2(X22,X23),X22)
        | ~ r2_hidden(esk3_2(X22,X23),X23)
        | X22 = X23 )
      & ( r2_hidden(esk3_2(X22,X23),X22)
        | r2_hidden(esk3_2(X22,X23),X23)
        | X22 = X23 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X2,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_34]),c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | r1_tarski(esk7_0,X2)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_14])).

fof(c_0_43,plain,(
    ! [X33,X34,X35,X36] :
      ( ( r2_hidden(esk4_4(X33,X34,X35,X36),X34)
        | ~ r1_tarski(X33,k2_zfmisc_1(X34,X35))
        | ~ r2_hidden(X36,X33) )
      & ( r2_hidden(esk5_4(X33,X34,X35,X36),X35)
        | ~ r1_tarski(X33,k2_zfmisc_1(X34,X35))
        | ~ r2_hidden(X36,X33) )
      & ( X36 = k4_tarski(esk4_4(X33,X34,X35,X36),esk5_4(X33,X34,X35,X36))
        | ~ r1_tarski(X33,k2_zfmisc_1(X34,X35))
        | ~ r2_hidden(X36,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_zfmisc_1])])])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk1_2(esk9_0,X1),esk7_0)
    | r1_tarski(esk9_0,X1)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_14])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_28])).

fof(c_0_47,plain,(
    ! [X25,X26] :
      ( ( r1_tarski(X25,X26)
        | X25 != X26 )
      & ( r1_tarski(X26,X25)
        | X25 != X26 )
      & ( ~ r1_tarski(X25,X26)
        | ~ r1_tarski(X26,X25)
        | X25 = X26 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_48,negated_conjecture,
    ( X1 = esk6_0
    | r2_hidden(esk3_2(X1,esk6_0),esk8_0)
    | r2_hidden(esk3_2(X1,esk6_0),X1)
    | r1_tarski(esk7_0,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_40])).

cnf(c_0_49,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk9_0,X1),esk7_0)
    | r1_tarski(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,X1),esk9_0)
    | r1_tarski(esk7_0,X1)
    | ~ r2_hidden(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_14])).

cnf(c_0_53,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,k1_xboole_0),esk9_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_45])).

cnf(c_0_54,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( esk8_0 = esk6_0
    | r2_hidden(esk3_2(esk8_0,esk6_0),esk8_0)
    | r1_tarski(esk7_0,X1) ),
    inference(ef,[status(thm)],[c_0_48])).

fof(c_0_56,plain,(
    ! [X27] : r1_tarski(k1_xboole_0,X27) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_57,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X5)
    | ~ r2_hidden(X4,X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r1_tarski(X2,X5) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r1_tarski(esk9_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk7_0,X1),esk9_0)
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_45])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X2,esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_33])).

cnf(c_0_62,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,k1_xboole_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_45])).

cnf(c_0_63,negated_conjecture,
    ( esk8_0 = esk6_0
    | X1 = esk7_0
    | r2_hidden(esk3_2(esk8_0,esk6_0),esk8_0)
    | ~ r1_tarski(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | ~ r1_tarski(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_57])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk9_0 = esk7_0
    | ~ r1_tarski(esk7_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk7_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 = esk6_0
    | r2_hidden(esk3_2(esk8_0,esk6_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,plain,
    ( r2_hidden(esk5_4(X1,X2,X3,X4),X3)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_74,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) != k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_75,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk9_0 = esk7_0
    | esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,plain,
    ( X1 = X2
    | ~ r2_hidden(esk3_2(X1,X2),X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_77,negated_conjecture,
    ( esk8_0 = esk6_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk8_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_71])).

cnf(c_0_79,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | k2_zfmisc_1(esk8_0,esk7_0) != k2_zfmisc_1(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk8_0 = esk6_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_70])).

cnf(c_0_82,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_66])).

cnf(c_0_83,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_tarski(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_45])).

cnf(c_0_86,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,k2_zfmisc_1(k1_xboole_0,X3)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_50])).

cnf(c_0_87,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_88,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_89,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ r1_tarski(esk8_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])])).

cnf(c_0_90,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_84]),c_0_85]),c_0_85])])).

cnf(c_0_91,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_66])).

cnf(c_0_92,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_45])).

cnf(c_0_93,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(X2,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_34])).

cnf(c_0_94,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_64])])).

cnf(c_0_95,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_45])).

cnf(c_0_96,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | r2_hidden(esk2_3(X1,X1,esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_94]),c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_94]),c_0_39])).

cnf(c_0_99,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_85])])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_99]),c_0_95])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n015.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 14:23:23 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.31  # Version: 2.5pre002
% 0.16/0.31  # No SInE strategy applied
% 0.16/0.31  # Trying AutoSched0 for 299 seconds
% 0.16/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.16/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.16/0.41  #
% 0.16/0.41  # Preprocessing time       : 0.028 s
% 0.16/0.41  # Presaturation interreduction done
% 0.16/0.41  
% 0.16/0.41  # Proof found!
% 0.16/0.41  # SZS status Theorem
% 0.16/0.41  # SZS output start CNFRefutation
% 0.16/0.41  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.16/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.16/0.41  fof(t108_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(![X5, X6]:(r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X1,X2))<=>r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X3,X4)))=>k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_zfmisc_1)).
% 0.16/0.41  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.16/0.41  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.16/0.41  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 0.16/0.41  fof(t103_zfmisc_1, axiom, ![X1, X2, X3, X4]:~(((r1_tarski(X1,k2_zfmisc_1(X2,X3))&r2_hidden(X4,X1))&![X5, X6]:~(((r2_hidden(X5,X2)&r2_hidden(X6,X3))&X4=k4_tarski(X5,X6))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 0.16/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.16/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.16/0.41  fof(c_0_9, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k4_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k4_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.16/0.41  cnf(c_0_10, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.41  fof(c_0_11, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.16/0.41  cnf(c_0_12, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.41  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_10])).
% 0.16/0.41  cnf(c_0_14, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.16/0.41  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4]:(![X5, X6]:(r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X1,X2))<=>r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X3,X4)))=>k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4))), inference(assume_negation,[status(cth)],[t108_zfmisc_1])).
% 0.16/0.41  cnf(c_0_16, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_12])).
% 0.16/0.41  fof(c_0_17, plain, ![X28]:(~r1_tarski(X28,k1_xboole_0)|X28=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.16/0.41  cnf(c_0_18, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.16/0.41  cnf(c_0_19, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)|r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.16/0.41  fof(c_0_20, plain, ![X29, X30, X31, X32]:(((r2_hidden(X29,X31)|~r2_hidden(k4_tarski(X29,X30),k2_zfmisc_1(X31,X32)))&(r2_hidden(X30,X32)|~r2_hidden(k4_tarski(X29,X30),k2_zfmisc_1(X31,X32))))&(~r2_hidden(X29,X31)|~r2_hidden(X30,X32)|r2_hidden(k4_tarski(X29,X30),k2_zfmisc_1(X31,X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.16/0.41  fof(c_0_21, negated_conjecture, ![X43, X44]:(((~r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(esk6_0,esk7_0))|r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(esk8_0,esk9_0)))&(~r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(esk8_0,esk9_0))|r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(esk6_0,esk7_0))))&k2_zfmisc_1(esk6_0,esk7_0)!=k2_zfmisc_1(esk8_0,esk9_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).
% 0.16/0.41  cnf(c_0_22, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_16, c_0_14])).
% 0.16/0.41  cnf(c_0_23, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.16/0.41  cnf(c_0_24, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.16/0.41  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.16/0.41  cnf(c_0_26, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk8_0,esk9_0))|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.16/0.41  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk6_0,esk7_0))|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.16/0.41  cnf(c_0_28, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.16/0.41  cnf(c_0_29, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_22, c_0_19])).
% 0.16/0.41  cnf(c_0_30, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.16/0.41  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.16/0.41  cnf(c_0_32, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.16/0.41  cnf(c_0_33, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk6_0,esk7_0))|~r2_hidden(X2,esk9_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.16/0.41  cnf(c_0_34, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_29])).
% 0.16/0.41  cnf(c_0_35, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_16, c_0_30])).
% 0.16/0.41  fof(c_0_36, plain, ![X22, X23]:((~r2_hidden(esk3_2(X22,X23),X22)|~r2_hidden(esk3_2(X22,X23),X23)|X22=X23)&(r2_hidden(esk3_2(X22,X23),X22)|r2_hidden(esk3_2(X22,X23),X23)|X22=X23)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.16/0.41  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X2,esk7_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_31, c_0_28])).
% 0.16/0.41  cnf(c_0_38, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk9_0)|~r2_hidden(X2,esk8_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.16/0.41  cnf(c_0_39, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_34]), c_0_35])).
% 0.16/0.41  cnf(c_0_40, plain, (r2_hidden(esk3_2(X1,X2),X1)|r2_hidden(esk3_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.16/0.41  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_32, c_0_26])).
% 0.16/0.41  cnf(c_0_42, negated_conjecture, (r2_hidden(X1,esk8_0)|r1_tarski(esk7_0,X2)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_37, c_0_14])).
% 0.16/0.41  fof(c_0_43, plain, ![X33, X34, X35, X36]:(((r2_hidden(esk4_4(X33,X34,X35,X36),X34)|(~r1_tarski(X33,k2_zfmisc_1(X34,X35))|~r2_hidden(X36,X33)))&(r2_hidden(esk5_4(X33,X34,X35,X36),X35)|(~r1_tarski(X33,k2_zfmisc_1(X34,X35))|~r2_hidden(X36,X33))))&(X36=k4_tarski(esk4_4(X33,X34,X35,X36),esk5_4(X33,X34,X35,X36))|(~r1_tarski(X33,k2_zfmisc_1(X34,X35))|~r2_hidden(X36,X33)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_zfmisc_1])])])])).
% 0.16/0.41  cnf(c_0_44, negated_conjecture, (r2_hidden(esk1_2(esk9_0,X1),esk7_0)|r1_tarski(esk9_0,X1)|~r2_hidden(X2,esk8_0)), inference(spm,[status(thm)],[c_0_38, c_0_14])).
% 0.16/0.41  cnf(c_0_45, plain, (X1=k1_xboole_0|r2_hidden(esk3_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.16/0.41  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(X1,esk7_0)|~r2_hidden(X2,esk6_0)), inference(spm,[status(thm)],[c_0_41, c_0_28])).
% 0.16/0.41  fof(c_0_47, plain, ![X25, X26]:(((r1_tarski(X25,X26)|X25!=X26)&(r1_tarski(X26,X25)|X25!=X26))&(~r1_tarski(X25,X26)|~r1_tarski(X26,X25)|X25=X26)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.16/0.41  cnf(c_0_48, negated_conjecture, (X1=esk6_0|r2_hidden(esk3_2(X1,esk6_0),esk8_0)|r2_hidden(esk3_2(X1,esk6_0),X1)|r1_tarski(esk7_0,X2)), inference(spm,[status(thm)],[c_0_42, c_0_40])).
% 0.16/0.41  cnf(c_0_49, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.16/0.41  cnf(c_0_50, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X2)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r2_hidden(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.16/0.41  cnf(c_0_51, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(esk1_2(esk9_0,X1),esk7_0)|r1_tarski(esk9_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.16/0.41  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_2(esk7_0,X1),esk9_0)|r1_tarski(esk7_0,X1)|~r2_hidden(X2,esk6_0)), inference(spm,[status(thm)],[c_0_46, c_0_14])).
% 0.16/0.41  cnf(c_0_53, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,k1_xboole_0),esk9_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_46, c_0_45])).
% 0.16/0.41  cnf(c_0_54, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.16/0.41  cnf(c_0_55, negated_conjecture, (esk8_0=esk6_0|r2_hidden(esk3_2(esk8_0,esk6_0),esk8_0)|r1_tarski(esk7_0,X1)), inference(ef,[status(thm)],[c_0_48])).
% 0.16/0.41  fof(c_0_56, plain, ![X27]:r1_tarski(k1_xboole_0,X27), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.16/0.41  cnf(c_0_57, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X5)|~r2_hidden(X4,X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r1_tarski(X2,X5)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.16/0.41  cnf(c_0_58, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.16/0.41  cnf(c_0_59, negated_conjecture, (esk8_0=k1_xboole_0|r1_tarski(esk9_0,esk7_0)), inference(spm,[status(thm)],[c_0_18, c_0_51])).
% 0.16/0.41  cnf(c_0_60, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk1_2(esk7_0,X1),esk9_0)|r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_52, c_0_45])).
% 0.16/0.41  cnf(c_0_61, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X2,esk9_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_25, c_0_33])).
% 0.16/0.41  cnf(c_0_62, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,k1_xboole_0),esk9_0)), inference(spm,[status(thm)],[c_0_53, c_0_45])).
% 0.16/0.41  cnf(c_0_63, negated_conjecture, (esk8_0=esk6_0|X1=esk7_0|r2_hidden(esk3_2(esk8_0,esk6_0),esk8_0)|~r1_tarski(X1,esk7_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.16/0.41  cnf(c_0_64, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.16/0.41  cnf(c_0_65, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,k2_zfmisc_1(X3,X4))|~r1_tarski(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_57])).
% 0.16/0.41  cnf(c_0_66, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_58])).
% 0.16/0.41  cnf(c_0_67, negated_conjecture, (esk8_0=k1_xboole_0|esk9_0=esk7_0|~r1_tarski(esk7_0,esk9_0)), inference(spm,[status(thm)],[c_0_54, c_0_59])).
% 0.16/0.41  cnf(c_0_68, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk7_0,esk9_0)), inference(spm,[status(thm)],[c_0_18, c_0_60])).
% 0.16/0.41  cnf(c_0_69, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.16/0.41  cnf(c_0_70, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0=esk6_0|r2_hidden(esk3_2(esk8_0,esk6_0),esk8_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.16/0.41  cnf(c_0_71, plain, (r2_hidden(esk5_4(X1,X2,X3,X4),X3)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r2_hidden(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.16/0.42  cnf(c_0_72, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,X3))|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.16/0.42  cnf(c_0_73, plain, (k1_xboole_0=X1|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.16/0.42  cnf(c_0_74, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)!=k2_zfmisc_1(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.16/0.42  cnf(c_0_75, negated_conjecture, (esk6_0=k1_xboole_0|esk9_0=esk7_0|esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.16/0.42  cnf(c_0_76, plain, (X1=X2|~r2_hidden(esk3_2(X1,X2),X1)|~r2_hidden(esk3_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.16/0.42  cnf(c_0_77, negated_conjecture, (esk8_0=esk6_0|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(esk3_2(esk8_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.16/0.42  cnf(c_0_78, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,k2_zfmisc_1(X3,k1_xboole_0))), inference(spm,[status(thm)],[c_0_39, c_0_71])).
% 0.16/0.42  cnf(c_0_79, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.16/0.42  cnf(c_0_80, negated_conjecture, (esk8_0=k1_xboole_0|esk6_0=k1_xboole_0|k2_zfmisc_1(esk8_0,esk7_0)!=k2_zfmisc_1(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.16/0.42  cnf(c_0_81, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|esk8_0=esk6_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_70])).
% 0.16/0.42  cnf(c_0_82, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_78, c_0_66])).
% 0.16/0.42  cnf(c_0_83, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)!=k1_xboole_0|~r1_tarski(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_79])).
% 0.16/0.42  cnf(c_0_84, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.16/0.42  cnf(c_0_85, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_82, c_0_45])).
% 0.16/0.42  cnf(c_0_86, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,k2_zfmisc_1(k1_xboole_0,X3))), inference(spm,[status(thm)],[c_0_39, c_0_50])).
% 0.16/0.42  cnf(c_0_87, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.42  cnf(c_0_88, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.42  cnf(c_0_89, negated_conjecture, (esk6_0=k1_xboole_0|~r1_tarski(esk8_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])])).
% 0.16/0.42  cnf(c_0_90, negated_conjecture, (esk6_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_84]), c_0_85]), c_0_85])])).
% 0.16/0.42  cnf(c_0_91, plain, (~r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_86, c_0_66])).
% 0.16/0.42  cnf(c_0_92, negated_conjecture, (esk9_0=k1_xboole_0|r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_61, c_0_45])).
% 0.16/0.42  cnf(c_0_93, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(X2,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_34])).
% 0.16/0.42  cnf(c_0_94, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_64])])).
% 0.16/0.42  cnf(c_0_95, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_91, c_0_45])).
% 0.16/0.42  cnf(c_0_96, negated_conjecture, (esk8_0=k1_xboole_0|esk9_0=k1_xboole_0|r2_hidden(esk2_3(X1,X1,esk8_0),esk6_0)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.16/0.42  cnf(c_0_97, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_94]), c_0_95])).
% 0.16/0.42  cnf(c_0_98, negated_conjecture, (esk9_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_94]), c_0_39])).
% 0.16/0.42  cnf(c_0_99, negated_conjecture, (esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_85])])).
% 0.16/0.42  cnf(c_0_100, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_99]), c_0_95])]), ['proof']).
% 0.16/0.42  # SZS output end CNFRefutation
% 0.16/0.42  # Proof object total steps             : 101
% 0.16/0.42  # Proof object clause steps            : 82
% 0.16/0.42  # Proof object formula steps           : 19
% 0.16/0.42  # Proof object conjectures             : 43
% 0.16/0.42  # Proof object clause conjectures      : 40
% 0.16/0.42  # Proof object formula conjectures     : 3
% 0.16/0.42  # Proof object initial clauses used    : 21
% 0.16/0.42  # Proof object initial formulas used   : 9
% 0.16/0.42  # Proof object generating inferences   : 55
% 0.16/0.42  # Proof object simplifying inferences  : 22
% 0.16/0.42  # Training examples: 0 positive, 0 negative
% 0.16/0.42  # Parsed axioms                        : 9
% 0.16/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.42  # Initial clauses                      : 25
% 0.16/0.42  # Removed in clause preprocessing      : 0
% 0.16/0.42  # Initial clauses in saturation        : 25
% 0.16/0.42  # Processed clauses                    : 707
% 0.16/0.42  # ...of these trivial                  : 0
% 0.16/0.42  # ...subsumed                          : 435
% 0.16/0.42  # ...remaining for further processing  : 272
% 0.16/0.42  # Other redundant clauses eliminated   : 5
% 0.16/0.42  # Clauses deleted for lack of memory   : 0
% 0.16/0.42  # Backward-subsumed                    : 26
% 0.16/0.42  # Backward-rewritten                   : 121
% 0.16/0.42  # Generated clauses                    : 3682
% 0.16/0.42  # ...of the previous two non-trivial   : 3698
% 0.16/0.42  # Contextual simplify-reflections      : 2
% 0.16/0.42  # Paramodulations                      : 3649
% 0.16/0.42  # Factorizations                       : 28
% 0.16/0.42  # Equation resolutions                 : 5
% 0.16/0.42  # Propositional unsat checks           : 0
% 0.16/0.42  #    Propositional check models        : 0
% 0.16/0.42  #    Propositional check unsatisfiable : 0
% 0.16/0.42  #    Propositional clauses             : 0
% 0.16/0.42  #    Propositional clauses after purity: 0
% 0.16/0.42  #    Propositional unsat core size     : 0
% 0.16/0.42  #    Propositional preprocessing time  : 0.000
% 0.16/0.42  #    Propositional encoding time       : 0.000
% 0.16/0.42  #    Propositional solver time         : 0.000
% 0.16/0.42  #    Success case prop preproc time    : 0.000
% 0.16/0.42  #    Success case prop encoding time   : 0.000
% 0.16/0.42  #    Success case prop solver time     : 0.000
% 0.16/0.42  # Current number of processed clauses  : 96
% 0.16/0.42  #    Positive orientable unit clauses  : 9
% 0.16/0.42  #    Positive unorientable unit clauses: 0
% 0.16/0.42  #    Negative unit clauses             : 1
% 0.16/0.42  #    Non-unit-clauses                  : 86
% 0.16/0.42  # Current number of unprocessed clauses: 3025
% 0.16/0.42  # ...number of literals in the above   : 12457
% 0.16/0.42  # Current number of archived formulas  : 0
% 0.16/0.42  # Current number of archived clauses   : 171
% 0.16/0.42  # Clause-clause subsumption calls (NU) : 5618
% 0.16/0.42  # Rec. Clause-clause subsumption calls : 2449
% 0.16/0.42  # Non-unit clause-clause subsumptions  : 310
% 0.16/0.42  # Unit Clause-clause subsumption calls : 128
% 0.16/0.42  # Rewrite failures with RHS unbound    : 0
% 0.16/0.42  # BW rewrite match attempts            : 15
% 0.16/0.42  # BW rewrite match successes           : 7
% 0.16/0.42  # Condensation attempts                : 0
% 0.16/0.42  # Condensation successes               : 0
% 0.16/0.42  # Termbank termtop insertions          : 50823
% 0.16/0.42  
% 0.16/0.42  # -------------------------------------------------
% 0.16/0.42  # User time                : 0.096 s
% 0.16/0.42  # System time              : 0.008 s
% 0.16/0.42  # Total time               : 0.105 s
% 0.16/0.42  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
