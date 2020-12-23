%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:26 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 748 expanded)
%              Number of clauses        :   60 ( 387 expanded)
%              Number of leaves         :    9 ( 185 expanded)
%              Depth                    :   24
%              Number of atoms          :  227 (2772 expanded)
%              Number of equality atoms :   93 ( 833 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(c_0_9,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_10,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X24,X25,X26,X27,X30,X31,X32,X33,X34,X35,X37,X38] :
      ( ( r2_hidden(esk3_4(X24,X25,X26,X27),X24)
        | ~ r2_hidden(X27,X26)
        | X26 != k2_zfmisc_1(X24,X25) )
      & ( r2_hidden(esk4_4(X24,X25,X26,X27),X25)
        | ~ r2_hidden(X27,X26)
        | X26 != k2_zfmisc_1(X24,X25) )
      & ( X27 = k4_tarski(esk3_4(X24,X25,X26,X27),esk4_4(X24,X25,X26,X27))
        | ~ r2_hidden(X27,X26)
        | X26 != k2_zfmisc_1(X24,X25) )
      & ( ~ r2_hidden(X31,X24)
        | ~ r2_hidden(X32,X25)
        | X30 != k4_tarski(X31,X32)
        | r2_hidden(X30,X26)
        | X26 != k2_zfmisc_1(X24,X25) )
      & ( ~ r2_hidden(esk5_3(X33,X34,X35),X35)
        | ~ r2_hidden(X37,X33)
        | ~ r2_hidden(X38,X34)
        | esk5_3(X33,X34,X35) != k4_tarski(X37,X38)
        | X35 = k2_zfmisc_1(X33,X34) )
      & ( r2_hidden(esk6_3(X33,X34,X35),X33)
        | r2_hidden(esk5_3(X33,X34,X35),X35)
        | X35 = k2_zfmisc_1(X33,X34) )
      & ( r2_hidden(esk7_3(X33,X34,X35),X34)
        | r2_hidden(esk5_3(X33,X34,X35),X35)
        | X35 = k2_zfmisc_1(X33,X34) )
      & ( esk5_3(X33,X34,X35) = k4_tarski(esk6_3(X33,X34,X35),esk7_3(X33,X34,X35))
        | r2_hidden(esk5_3(X33,X34,X35),X35)
        | X35 = k2_zfmisc_1(X33,X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_12,plain,(
    ! [X17,X18] :
      ( ( k4_xboole_0(X17,X18) != k1_xboole_0
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | k4_xboole_0(X17,X18) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_13,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X21] : k4_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( X1 != k2_zfmisc_1(X2,X3)
    | ~ r2_hidden(X4,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_15])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X2) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_26])).

cnf(c_0_28,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,plain,
    ( X1 != k2_zfmisc_1(X2,k1_xboole_0)
    | ~ r2_hidden(X3,X1)
    | ~ v1_xboole_0(X4) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_30,plain,(
    ! [X41,X42,X43,X45,X46,X47,X48,X50] :
      ( ( r2_hidden(X43,esk8_3(X41,X42,X43))
        | ~ r2_hidden(X43,X42)
        | X42 != k3_tarski(X41) )
      & ( r2_hidden(esk8_3(X41,X42,X43),X41)
        | ~ r2_hidden(X43,X42)
        | X42 != k3_tarski(X41) )
      & ( ~ r2_hidden(X45,X46)
        | ~ r2_hidden(X46,X41)
        | r2_hidden(X45,X42)
        | X42 != k3_tarski(X41) )
      & ( ~ r2_hidden(esk9_2(X47,X48),X48)
        | ~ r2_hidden(esk9_2(X47,X48),X50)
        | ~ r2_hidden(X50,X47)
        | X48 = k3_tarski(X47) )
      & ( r2_hidden(esk9_2(X47,X48),esk10_2(X47,X48))
        | r2_hidden(esk9_2(X47,X48),X48)
        | X48 = k3_tarski(X47) )
      & ( r2_hidden(esk10_2(X47,X48),X47)
        | r2_hidden(esk9_2(X47,X48),X48)
        | X48 = k3_tarski(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0))
    | ~ v1_xboole_0(X3) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_32,plain,
    ( r2_hidden(esk8_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_33,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_34,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_35,plain,
    ( X1 != k3_tarski(X2)
    | ~ r2_hidden(X3,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_32])).

cnf(c_0_36,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X1)
    | X1 != k3_tarski(X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_23])).

cnf(c_0_38,plain,
    ( X1 != k2_zfmisc_1(X2,X3)
    | ~ r2_hidden(X4,X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_28])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_36])).

cnf(c_0_40,plain,
    ( v1_xboole_0(k3_tarski(X1))
    | ~ v1_xboole_0(X1) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_41,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_34])])).

cnf(c_0_42,plain,
    ( X1 != k3_tarski(X2)
    | X3 != k3_tarski(X1)
    | ~ r2_hidden(X4,X3)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_32])).

fof(c_0_43,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

cnf(c_0_44,plain,
    ( k3_tarski(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_40])).

cnf(c_0_45,plain,
    ( X1 != k2_zfmisc_1(X2,X3)
    | X3 != k1_xboole_0
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_28])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X1)
    | X2 != k3_tarski(X3)
    | X1 != k3_tarski(X2)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_23])).

fof(c_0_47,negated_conjecture,
    ( ( esk11_0 != k1_xboole_0
      | k2_zfmisc_1(esk11_0,esk12_0) != k1_xboole_0 )
    & ( esk12_0 != k1_xboole_0
      | k2_zfmisc_1(esk11_0,esk12_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk11_0,esk12_0) = k1_xboole_0
      | esk11_0 = k1_xboole_0
      | esk12_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | X1 != k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_44])).

cnf(c_0_49,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k2_zfmisc_1(X3,X1)) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X1)
    | X1 != k3_tarski(k3_tarski(X2))
    | ~ v1_xboole_0(X2) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( esk11_0 != k1_xboole_0
    | k2_zfmisc_1(esk11_0,esk12_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,plain,
    ( v1_xboole_0(X1)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_34])).

cnf(c_0_53,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_23])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X1)
    | X1 != k3_tarski(k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( k2_zfmisc_1(esk11_0,esk12_0) = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( esk11_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_26]),c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( esk12_0 != k1_xboole_0
    | k2_zfmisc_1(esk11_0,esk12_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_53])).

cnf(c_0_59,plain,
    ( v1_xboole_0(k3_tarski(k1_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k2_zfmisc_1(esk11_0,esk12_0) = k1_xboole_0
    | esk12_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( esk12_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_63,plain,
    ( v1_xboole_0(k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_34])).

cnf(c_0_64,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_65,negated_conjecture,
    ( k2_zfmisc_1(esk11_0,esk12_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_39]),c_0_34])])).

cnf(c_0_67,plain,
    ( r2_hidden(esk10_2(X1,X2),X1)
    | r2_hidden(esk9_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_68,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( X1 != k4_tarski(X2,X3)
    | X4 != k1_xboole_0
    | ~ r2_hidden(X3,esk12_0)
    | ~ r2_hidden(X2,esk11_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_41])).

cnf(c_0_70,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk9_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

fof(c_0_71,plain,(
    ! [X22,X23] : r1_tarski(X22,k2_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_72,negated_conjecture,
    ( X1 != k4_tarski(X2,esk9_2(k1_xboole_0,esk12_0))
    | X3 != k1_xboole_0
    | ~ r2_hidden(X2,esk11_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_61])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,esk11_0) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_75,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( X1 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_70]),c_0_56])).

cnf(c_0_77,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_75,c_0_76]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.19/0.47  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.029 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.47  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.47  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.19/0.47  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.47  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.47  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 0.19/0.47  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.47  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.47  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.47  fof(c_0_9, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.47  fof(c_0_10, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.47  fof(c_0_11, plain, ![X24, X25, X26, X27, X30, X31, X32, X33, X34, X35, X37, X38]:(((((r2_hidden(esk3_4(X24,X25,X26,X27),X24)|~r2_hidden(X27,X26)|X26!=k2_zfmisc_1(X24,X25))&(r2_hidden(esk4_4(X24,X25,X26,X27),X25)|~r2_hidden(X27,X26)|X26!=k2_zfmisc_1(X24,X25)))&(X27=k4_tarski(esk3_4(X24,X25,X26,X27),esk4_4(X24,X25,X26,X27))|~r2_hidden(X27,X26)|X26!=k2_zfmisc_1(X24,X25)))&(~r2_hidden(X31,X24)|~r2_hidden(X32,X25)|X30!=k4_tarski(X31,X32)|r2_hidden(X30,X26)|X26!=k2_zfmisc_1(X24,X25)))&((~r2_hidden(esk5_3(X33,X34,X35),X35)|(~r2_hidden(X37,X33)|~r2_hidden(X38,X34)|esk5_3(X33,X34,X35)!=k4_tarski(X37,X38))|X35=k2_zfmisc_1(X33,X34))&(((r2_hidden(esk6_3(X33,X34,X35),X33)|r2_hidden(esk5_3(X33,X34,X35),X35)|X35=k2_zfmisc_1(X33,X34))&(r2_hidden(esk7_3(X33,X34,X35),X34)|r2_hidden(esk5_3(X33,X34,X35),X35)|X35=k2_zfmisc_1(X33,X34)))&(esk5_3(X33,X34,X35)=k4_tarski(esk6_3(X33,X34,X35),esk7_3(X33,X34,X35))|r2_hidden(esk5_3(X33,X34,X35),X35)|X35=k2_zfmisc_1(X33,X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.19/0.47  fof(c_0_12, plain, ![X17, X18]:((k4_xboole_0(X17,X18)!=k1_xboole_0|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|k4_xboole_0(X17,X18)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.47  cnf(c_0_13, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.47  cnf(c_0_14, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.47  cnf(c_0_15, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.47  fof(c_0_16, plain, ![X21]:k4_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.47  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.47  cnf(c_0_18, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.47  cnf(c_0_19, plain, (X1!=k2_zfmisc_1(X2,X3)|~r2_hidden(X4,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_13, c_0_15])).
% 0.19/0.47  cnf(c_0_20, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.47  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.47  cnf(c_0_22, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X2)), inference(er,[status(thm)],[c_0_19])).
% 0.19/0.47  cnf(c_0_23, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.47  cnf(c_0_24, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.47  cnf(c_0_25, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.47  cnf(c_0_26, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.47  cnf(c_0_27, plain, (~r2_hidden(X1,k1_xboole_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_22, c_0_26])).
% 0.19/0.47  cnf(c_0_28, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.47  cnf(c_0_29, plain, (X1!=k2_zfmisc_1(X2,k1_xboole_0)|~r2_hidden(X3,X1)|~v1_xboole_0(X4)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.47  fof(c_0_30, plain, ![X41, X42, X43, X45, X46, X47, X48, X50]:((((r2_hidden(X43,esk8_3(X41,X42,X43))|~r2_hidden(X43,X42)|X42!=k3_tarski(X41))&(r2_hidden(esk8_3(X41,X42,X43),X41)|~r2_hidden(X43,X42)|X42!=k3_tarski(X41)))&(~r2_hidden(X45,X46)|~r2_hidden(X46,X41)|r2_hidden(X45,X42)|X42!=k3_tarski(X41)))&((~r2_hidden(esk9_2(X47,X48),X48)|(~r2_hidden(esk9_2(X47,X48),X50)|~r2_hidden(X50,X47))|X48=k3_tarski(X47))&((r2_hidden(esk9_2(X47,X48),esk10_2(X47,X48))|r2_hidden(esk9_2(X47,X48),X48)|X48=k3_tarski(X47))&(r2_hidden(esk10_2(X47,X48),X47)|r2_hidden(esk9_2(X47,X48),X48)|X48=k3_tarski(X47))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.19/0.47  cnf(c_0_31, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0))|~v1_xboole_0(X3)), inference(er,[status(thm)],[c_0_29])).
% 0.19/0.47  cnf(c_0_32, plain, (r2_hidden(esk8_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.47  cnf(c_0_33, plain, (v1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_31, c_0_23])).
% 0.19/0.47  cnf(c_0_34, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.47  cnf(c_0_35, plain, (X1!=k3_tarski(X2)|~r2_hidden(X3,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_13, c_0_32])).
% 0.19/0.47  cnf(c_0_36, plain, (v1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.47  cnf(c_0_37, plain, (v1_xboole_0(X1)|X1!=k3_tarski(X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_35, c_0_23])).
% 0.19/0.47  cnf(c_0_38, plain, (X1!=k2_zfmisc_1(X2,X3)|~r2_hidden(X4,X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_13, c_0_28])).
% 0.19/0.47  cnf(c_0_39, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_36])).
% 0.19/0.47  cnf(c_0_40, plain, (v1_xboole_0(k3_tarski(X1))|~v1_xboole_0(X1)), inference(er,[status(thm)],[c_0_37])).
% 0.19/0.47  cnf(c_0_41, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_34])])).
% 0.19/0.47  cnf(c_0_42, plain, (X1!=k3_tarski(X2)|X3!=k3_tarski(X1)|~r2_hidden(X4,X3)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_35, c_0_32])).
% 0.19/0.47  fof(c_0_43, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.19/0.47  cnf(c_0_44, plain, (k3_tarski(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_24, c_0_40])).
% 0.19/0.47  cnf(c_0_45, plain, (X1!=k2_zfmisc_1(X2,X3)|X3!=k1_xboole_0|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_41, c_0_28])).
% 0.19/0.47  cnf(c_0_46, plain, (v1_xboole_0(X1)|X2!=k3_tarski(X3)|X1!=k3_tarski(X2)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_42, c_0_23])).
% 0.19/0.47  fof(c_0_47, negated_conjecture, (((esk11_0!=k1_xboole_0|k2_zfmisc_1(esk11_0,esk12_0)!=k1_xboole_0)&(esk12_0!=k1_xboole_0|k2_zfmisc_1(esk11_0,esk12_0)!=k1_xboole_0))&(k2_zfmisc_1(esk11_0,esk12_0)=k1_xboole_0|(esk11_0=k1_xboole_0|esk12_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])])).
% 0.19/0.47  cnf(c_0_48, plain, (v1_xboole_0(X1)|X1!=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_37, c_0_44])).
% 0.19/0.47  cnf(c_0_49, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k2_zfmisc_1(X3,X1))), inference(er,[status(thm)],[c_0_45])).
% 0.19/0.47  cnf(c_0_50, plain, (v1_xboole_0(X1)|X1!=k3_tarski(k3_tarski(X2))|~v1_xboole_0(X2)), inference(er,[status(thm)],[c_0_46])).
% 0.19/0.47  cnf(c_0_51, negated_conjecture, (esk11_0!=k1_xboole_0|k2_zfmisc_1(esk11_0,esk12_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.47  cnf(c_0_52, plain, (v1_xboole_0(X1)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_34])).
% 0.19/0.47  cnf(c_0_53, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_23])).
% 0.19/0.47  cnf(c_0_54, plain, (v1_xboole_0(X1)|X1!=k3_tarski(k1_xboole_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_50, c_0_44])).
% 0.19/0.47  cnf(c_0_55, negated_conjecture, (k2_zfmisc_1(esk11_0,esk12_0)=k1_xboole_0|esk11_0=k1_xboole_0|esk12_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.47  cnf(c_0_56, negated_conjecture, (esk11_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_26]), c_0_52])).
% 0.19/0.47  cnf(c_0_57, negated_conjecture, (esk12_0!=k1_xboole_0|k2_zfmisc_1(esk11_0,esk12_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.47  cnf(c_0_58, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_53])).
% 0.19/0.47  cnf(c_0_59, plain, (v1_xboole_0(k3_tarski(k1_xboole_0))|~v1_xboole_0(X1)), inference(er,[status(thm)],[c_0_54])).
% 0.19/0.47  cnf(c_0_60, negated_conjecture, (k2_zfmisc_1(esk11_0,esk12_0)=k1_xboole_0|esk12_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.47  cnf(c_0_61, negated_conjecture, (esk12_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.47  cnf(c_0_62, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X3)), inference(er,[status(thm)],[c_0_38])).
% 0.19/0.47  cnf(c_0_63, plain, (v1_xboole_0(k3_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_59, c_0_34])).
% 0.19/0.47  cnf(c_0_64, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.47  cnf(c_0_65, negated_conjecture, (k2_zfmisc_1(esk11_0,esk12_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.47  cnf(c_0_66, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_39]), c_0_34])])).
% 0.19/0.47  cnf(c_0_67, plain, (r2_hidden(esk10_2(X1,X2),X1)|r2_hidden(esk9_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.47  cnf(c_0_68, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_63])).
% 0.19/0.47  cnf(c_0_69, negated_conjecture, (X1!=k4_tarski(X2,X3)|X4!=k1_xboole_0|~r2_hidden(X3,esk12_0)|~r2_hidden(X2,esk11_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_41])).
% 0.19/0.47  cnf(c_0_70, plain, (X1=k1_xboole_0|r2_hidden(esk9_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 0.19/0.47  fof(c_0_71, plain, ![X22, X23]:r1_tarski(X22,k2_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.47  cnf(c_0_72, negated_conjecture, (X1!=k4_tarski(X2,esk9_2(k1_xboole_0,esk12_0))|X3!=k1_xboole_0|~r2_hidden(X2,esk11_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_61])).
% 0.19/0.47  cnf(c_0_73, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.47  cnf(c_0_74, negated_conjecture, (X1!=k1_xboole_0|~r2_hidden(X2,esk11_0)), inference(er,[status(thm)],[c_0_72])).
% 0.19/0.47  cnf(c_0_75, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_17, c_0_73])).
% 0.19/0.47  cnf(c_0_76, negated_conjecture, (X1!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_70]), c_0_56])).
% 0.19/0.47  cnf(c_0_77, plain, ($false), inference(sr,[status(thm)],[c_0_75, c_0_76]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 78
% 0.19/0.47  # Proof object clause steps            : 60
% 0.19/0.47  # Proof object formula steps           : 18
% 0.19/0.47  # Proof object conjectures             : 14
% 0.19/0.47  # Proof object clause conjectures      : 11
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 15
% 0.19/0.47  # Proof object initial formulas used   : 9
% 0.19/0.47  # Proof object generating inferences   : 42
% 0.19/0.47  # Proof object simplifying inferences  : 12
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 10
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 28
% 0.19/0.47  # Removed in clause preprocessing      : 0
% 0.19/0.47  # Initial clauses in saturation        : 28
% 0.19/0.47  # Processed clauses                    : 1670
% 0.19/0.47  # ...of these trivial                  : 15
% 0.19/0.47  # ...subsumed                          : 1291
% 0.19/0.47  # ...remaining for further processing  : 364
% 0.19/0.47  # Other redundant clauses eliminated   : 1
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 29
% 0.19/0.47  # Backward-rewritten                   : 14
% 0.19/0.47  # Generated clauses                    : 6005
% 0.19/0.47  # ...of the previous two non-trivial   : 5203
% 0.19/0.47  # Contextual simplify-reflections      : 4
% 0.19/0.47  # Paramodulations                      : 5900
% 0.19/0.47  # Factorizations                       : 0
% 0.19/0.47  # Equation resolutions                 : 93
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 281
% 0.19/0.47  #    Positive orientable unit clauses  : 8
% 0.19/0.47  #    Positive unorientable unit clauses: 0
% 0.19/0.47  #    Negative unit clauses             : 4
% 0.19/0.47  #    Non-unit-clauses                  : 269
% 0.19/0.47  # Current number of unprocessed clauses: 3505
% 0.19/0.47  # ...number of literals in the above   : 16931
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 83
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 8924
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 5540
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 845
% 0.19/0.47  # Unit Clause-clause subsumption calls : 172
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 16
% 0.19/0.47  # BW rewrite match successes           : 9
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 53414
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.128 s
% 0.19/0.47  # System time              : 0.004 s
% 0.19/0.47  # Total time               : 0.131 s
% 0.19/0.47  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
