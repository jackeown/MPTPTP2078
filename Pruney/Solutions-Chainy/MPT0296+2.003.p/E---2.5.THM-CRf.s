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
% DateTime   : Thu Dec  3 10:43:24 EST 2020

% Result     : Theorem 53.57s
% Output     : CNFRefutation 53.57s
% Verified   : 
% Statistics : Number of formulae       :  130 (9980 expanded)
%              Number of clauses        :  113 (5801 expanded)
%              Number of leaves         :    8 (2081 expanded)
%              Depth                    :   32
%              Number of atoms          :  374 (54850 expanded)
%              Number of equality atoms :  127 (18707 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(t68_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t60_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,X2)
     => ( ( r2_hidden(X3,X2)
          & X1 != X3 )
        | k3_xboole_0(k2_tarski(X1,X3),X2) = k1_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

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

fof(t104_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ~ ( r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))
        & ! [X6,X7] :
            ~ ( X1 = k4_tarski(X6,X7)
              & r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X7,k3_xboole_0(X3,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_8,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( r2_hidden(X20,X17)
        | ~ r2_hidden(X20,X19)
        | X19 != k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | X19 != k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X21,X17)
        | r2_hidden(X21,X18)
        | r2_hidden(X21,X19)
        | X19 != k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk2_3(X22,X23,X24),X24)
        | ~ r2_hidden(esk2_3(X22,X23,X24),X22)
        | r2_hidden(esk2_3(X22,X23,X24),X23)
        | X24 = k4_xboole_0(X22,X23) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X22)
        | r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k4_xboole_0(X22,X23) )
      & ( ~ r2_hidden(esk2_3(X22,X23,X24),X23)
        | r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k4_xboole_0(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_10,plain,(
    ! [X57,X58] :
      ( ( k4_xboole_0(k1_tarski(X57),X58) != k1_xboole_0
        | r2_hidden(X57,X58) )
      & ( ~ r2_hidden(X57,X58)
        | k4_xboole_0(k1_tarski(X57),X58) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_zfmisc_1])])).

fof(c_0_11,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X11,X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | ~ r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X14)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0
    | ~ r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),X2)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_18,plain,(
    ! [X54,X55,X56] :
      ( ( r2_hidden(X56,X55)
        | k3_xboole_0(k2_tarski(X54,X56),X55) = k1_tarski(X54)
        | ~ r2_hidden(X54,X55) )
      & ( X54 != X56
        | k3_xboole_0(k2_tarski(X54,X56),X55) = k1_tarski(X54)
        | ~ r2_hidden(X54,X55) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_20,plain,
    ( k3_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    | X1 != X2
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0
    | k3_xboole_0(X2,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( k3_xboole_0(k2_tarski(X1,X1),X2) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k1_tarski(X1) = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_28,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_29,plain,(
    ! [X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X28,X27)
        | X28 = X26
        | X27 != k1_tarski(X26) )
      & ( X29 != X26
        | r2_hidden(X29,X27)
        | X27 != k1_tarski(X26) )
      & ( ~ r2_hidden(esk3_2(X30,X31),X31)
        | esk3_2(X30,X31) != X30
        | X31 = k1_tarski(X30) )
      & ( r2_hidden(esk3_2(X30,X31),X31)
        | esk3_2(X30,X31) = X30
        | X31 = k1_tarski(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_26]),c_0_27])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0
    | k4_xboole_0(k1_xboole_0,X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k2_tarski(X2,X2))
    | ~ r2_hidden(X1,k1_tarski(X2))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_16]),c_0_16])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_41,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_37]),c_0_27])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_38,c_0_16])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_36])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_50,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_44]),c_0_45])])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_16])).

cnf(c_0_52,plain,
    ( esk1_3(k1_tarski(X1),X2,k1_xboole_0) = X1
    | k3_xboole_0(k1_tarski(X1),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_54,plain,
    ( k3_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_50])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_51])).

cnf(c_0_56,plain,
    ( k3_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_52]),c_0_42])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X1,k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_16])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,k1_tarski(X2)) = k1_tarski(X2)
    | ~ r2_hidden(X2,k3_xboole_0(X1,k1_tarski(X2))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,k1_tarski(X2)) = k1_xboole_0
    | r2_hidden(X2,k3_xboole_0(X1,k1_tarski(X2))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_55])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_57])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_58])).

fof(c_0_63,plain,(
    ! [X33,X34,X35,X36,X39,X40,X41,X42,X43,X44,X46,X47] :
      ( ( r2_hidden(esk4_4(X33,X34,X35,X36),X33)
        | ~ r2_hidden(X36,X35)
        | X35 != k2_zfmisc_1(X33,X34) )
      & ( r2_hidden(esk5_4(X33,X34,X35,X36),X34)
        | ~ r2_hidden(X36,X35)
        | X35 != k2_zfmisc_1(X33,X34) )
      & ( X36 = k4_tarski(esk4_4(X33,X34,X35,X36),esk5_4(X33,X34,X35,X36))
        | ~ r2_hidden(X36,X35)
        | X35 != k2_zfmisc_1(X33,X34) )
      & ( ~ r2_hidden(X40,X33)
        | ~ r2_hidden(X41,X34)
        | X39 != k4_tarski(X40,X41)
        | r2_hidden(X39,X35)
        | X35 != k2_zfmisc_1(X33,X34) )
      & ( ~ r2_hidden(esk6_3(X42,X43,X44),X44)
        | ~ r2_hidden(X46,X42)
        | ~ r2_hidden(X47,X43)
        | esk6_3(X42,X43,X44) != k4_tarski(X46,X47)
        | X44 = k2_zfmisc_1(X42,X43) )
      & ( r2_hidden(esk7_3(X42,X43,X44),X42)
        | r2_hidden(esk6_3(X42,X43,X44),X44)
        | X44 = k2_zfmisc_1(X42,X43) )
      & ( r2_hidden(esk8_3(X42,X43,X44),X43)
        | r2_hidden(esk6_3(X42,X43,X44),X44)
        | X44 = k2_zfmisc_1(X42,X43) )
      & ( esk6_3(X42,X43,X44) = k4_tarski(esk7_3(X42,X43,X44),esk8_3(X42,X43,X44))
        | r2_hidden(esk6_3(X42,X43,X44),X44)
        | X44 = k2_zfmisc_1(X42,X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_64,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ~ ( r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))
          & ! [X6,X7] :
              ~ ( X1 = k4_tarski(X6,X7)
                & r2_hidden(X6,k3_xboole_0(X2,X4))
                & r2_hidden(X7,k3_xboole_0(X3,X5)) ) ) ),
    inference(assume_negation,[status(cth)],[t104_zfmisc_1])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k1_tarski(X2)) = k1_tarski(X2)
    | k3_xboole_0(X1,k1_tarski(X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    | ~ r2_hidden(X1,k4_xboole_0(k1_tarski(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_61])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k4_xboole_0(k1_tarski(X1),X2))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_36])).

cnf(c_0_69,plain,
    ( r2_hidden(esk5_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_70,negated_conjecture,(
    ! [X64,X65] :
      ( r2_hidden(esk9_0,k3_xboole_0(k2_zfmisc_1(esk10_0,esk11_0),k2_zfmisc_1(esk12_0,esk13_0)))
      & ( esk9_0 != k4_tarski(X64,X65)
        | ~ r2_hidden(X64,k3_xboole_0(esk10_0,esk12_0))
        | ~ r2_hidden(X65,k3_xboole_0(esk11_0,esk13_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_64])])])])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,k1_tarski(X2)) = k1_xboole_0
    | k1_tarski(X2) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_66])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_74,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | k3_xboole_0(k2_tarski(X3,X1),X2) = k1_tarski(X3)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_76,plain,
    ( r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk9_0,k3_xboole_0(k2_zfmisc_1(esk10_0,esk11_0),k2_zfmisc_1(esk12_0,esk13_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_28]),c_0_37])).

cnf(c_0_79,plain,
    ( k1_tarski(X1) != k1_xboole_0
    | ~ r2_hidden(X2,k1_tarski(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_42])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,X2)
    | k1_tarski(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,plain,
    ( k3_xboole_0(k2_tarski(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X4),X2) = k1_tarski(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3))
    | r2_hidden(X4,X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk9_0,k2_zfmisc_1(esk12_0,esk13_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_77])).

cnf(c_0_83,plain,
    ( esk2_3(k1_xboole_0,X1,k1_tarski(X2)) = X2
    | k1_tarski(X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_78])).

cnf(c_0_84,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_36]),c_0_80])).

cnf(c_0_85,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_86,plain,(
    ! [X50,X51,X52,X53] :
      ( ( r2_hidden(X50,X52)
        | ~ r2_hidden(k4_tarski(X50,X51),k2_zfmisc_1(X52,X53)) )
      & ( r2_hidden(X51,X53)
        | ~ r2_hidden(k4_tarski(X50,X51),k2_zfmisc_1(X52,X53)) )
      & ( ~ r2_hidden(X50,X52)
        | ~ r2_hidden(X51,X53)
        | r2_hidden(k4_tarski(X50,X51),k2_zfmisc_1(X52,X53)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_87,plain,
    ( X1 = k4_tarski(esk4_4(X2,X3,X4,X1),esk5_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_88,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,X3,k3_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_78])).

cnf(c_0_89,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk5_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),X1),esk13_0) = k1_tarski(esk5_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0))
    | r2_hidden(X1,esk13_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_90,plain,
    ( esk2_3(k1_xboole_0,X1,k1_tarski(X2)) = X2 ),
    inference(sr,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk9_0,k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_77])).

cnf(c_0_92,plain,
    ( r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_85])).

cnf(c_0_93,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_94,plain,
    ( k4_tarski(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk5_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),esk13_0)
    | r2_hidden(X1,esk13_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90]),c_0_84])).

cnf(c_0_96,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk5_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0),X1),esk11_0) = k1_tarski(esk5_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0))
    | r2_hidden(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_91])).

cnf(c_0_97,plain,
    ( esk4_4(k1_tarski(X1),X2,k2_zfmisc_1(k1_tarski(X1),X2),X3) = X1
    | ~ r2_hidden(X3,k2_zfmisc_1(k1_tarski(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_92])).

cnf(c_0_98,plain,
    ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(esk5_4(X4,X5,k2_zfmisc_1(X4,X5),X1),X3)
    | ~ r2_hidden(esk4_4(X4,X5,k2_zfmisc_1(X4,X5),X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X4,X5)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk5_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),esk13_0) ),
    inference(ef,[status(thm)],[c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(esk5_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0),esk11_0)
    | r2_hidden(X1,esk11_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_96]),c_0_90]),c_0_84])).

cnf(c_0_101,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_102,plain,
    ( k4_tarski(X1,esk5_4(k1_tarski(X1),X2,k2_zfmisc_1(k1_tarski(X1),X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(k1_tarski(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(esk9_0,k2_zfmisc_1(X1,esk13_0))
    | ~ r2_hidden(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_82])])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(esk5_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0),esk11_0) ),
    inference(ef,[status(thm)],[c_0_100])).

cnf(c_0_105,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(k1_tarski(X1),X4))
    | ~ r2_hidden(X3,k2_zfmisc_1(X2,X5)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(esk9_0,k2_zfmisc_1(k1_tarski(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0)),esk13_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_36])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk9_0,k2_zfmisc_1(X1,esk11_0))
    | ~ r2_hidden(esk4_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_104]),c_0_91])])).

cnf(c_0_108,negated_conjecture,
    ( esk9_0 != k4_tarski(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(esk10_0,esk12_0))
    | ~ r2_hidden(X2,k3_xboole_0(esk11_0,esk13_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_109,plain,
    ( k3_xboole_0(k2_tarski(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X4),X1) = k1_tarski(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3))
    | r2_hidden(X4,X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_92])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),X1)
    | ~ r2_hidden(esk9_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(esk9_0,k2_zfmisc_1(k1_tarski(esk4_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0)),esk11_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_36])).

cnf(c_0_112,negated_conjecture,
    ( k4_tarski(X1,X2) != esk9_0
    | ~ r2_hidden(X1,k3_xboole_0(esk10_0,esk12_0))
    | ~ r2_hidden(X2,esk13_0)
    | ~ r2_hidden(X2,esk11_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_71])).

cnf(c_0_113,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),X1),esk12_0) = k1_tarski(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0))
    | r2_hidden(X1,esk12_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_82])).

cnf(c_0_114,negated_conjecture,
    ( r2_hidden(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),k1_tarski(esk4_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0))) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( k4_tarski(X1,X2) != esk9_0
    | ~ r2_hidden(X2,esk13_0)
    | ~ r2_hidden(X2,esk11_0)
    | ~ r2_hidden(X1,esk12_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_71])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),esk12_0)
    | r2_hidden(X1,esk12_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_113]),c_0_90]),c_0_84])).

cnf(c_0_117,negated_conjecture,
    ( esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0) = esk4_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_114])).

cnf(c_0_118,negated_conjecture,
    ( r2_hidden(esk4_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0),X1)
    | ~ r2_hidden(esk9_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_111])).

cnf(c_0_119,negated_conjecture,
    ( ~ r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),esk9_0),esk13_0)
    | ~ r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),esk9_0),esk11_0)
    | ~ r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),esk9_0),esk12_0)
    | ~ r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),esk9_0),esk10_0)
    | ~ r2_hidden(esk9_0,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_94])])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),esk12_0) ),
    inference(ef,[status(thm)],[c_0_116])).

cnf(c_0_121,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_122,negated_conjecture,
    ( k4_tarski(esk4_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0),esk5_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0)) = esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_117]),c_0_82])])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(esk4_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_82])).

cnf(c_0_124,negated_conjecture,
    ( ~ r2_hidden(esk5_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),esk11_0)
    | ~ r2_hidden(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_99]),c_0_120]),c_0_82])])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_91])).

cnf(c_0_126,negated_conjecture,
    ( r2_hidden(esk5_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),X1)
    | ~ r2_hidden(esk9_0,k2_zfmisc_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(esk9_0,k2_zfmisc_1(esk12_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_123])).

cnf(c_0_128,negated_conjecture,
    ( ~ r2_hidden(esk5_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_125])])).

cnf(c_0_129,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_128]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:24:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 53.57/53.80  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 53.57/53.80  # and selection function SelectComplexExceptUniqMaxHorn.
% 53.57/53.80  #
% 53.57/53.80  # Preprocessing time       : 0.028 s
% 53.57/53.80  # Presaturation interreduction done
% 53.57/53.80  
% 53.57/53.80  # Proof found!
% 53.57/53.80  # SZS status Theorem
% 53.57/53.80  # SZS output start CNFRefutation
% 53.57/53.80  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 53.57/53.80  fof(t68_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 53.57/53.80  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 53.57/53.80  fof(t60_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,X2)=>((r2_hidden(X3,X2)&X1!=X3)|k3_xboole_0(k2_tarski(X1,X3),X2)=k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_zfmisc_1)).
% 53.57/53.80  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 53.57/53.80  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 53.57/53.80  fof(t104_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5]:~((r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))&![X6, X7]:~(((X1=k4_tarski(X6,X7)&r2_hidden(X6,k3_xboole_0(X2,X4)))&r2_hidden(X7,k3_xboole_0(X3,X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_zfmisc_1)).
% 53.57/53.80  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 53.57/53.80  fof(c_0_8, plain, ![X17, X18, X19, X20, X21, X22, X23, X24]:((((r2_hidden(X20,X17)|~r2_hidden(X20,X19)|X19!=k4_xboole_0(X17,X18))&(~r2_hidden(X20,X18)|~r2_hidden(X20,X19)|X19!=k4_xboole_0(X17,X18)))&(~r2_hidden(X21,X17)|r2_hidden(X21,X18)|r2_hidden(X21,X19)|X19!=k4_xboole_0(X17,X18)))&((~r2_hidden(esk2_3(X22,X23,X24),X24)|(~r2_hidden(esk2_3(X22,X23,X24),X22)|r2_hidden(esk2_3(X22,X23,X24),X23))|X24=k4_xboole_0(X22,X23))&((r2_hidden(esk2_3(X22,X23,X24),X22)|r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k4_xboole_0(X22,X23))&(~r2_hidden(esk2_3(X22,X23,X24),X23)|r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k4_xboole_0(X22,X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 53.57/53.80  cnf(c_0_9, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 53.57/53.80  fof(c_0_10, plain, ![X57, X58]:((k4_xboole_0(k1_tarski(X57),X58)!=k1_xboole_0|r2_hidden(X57,X58))&(~r2_hidden(X57,X58)|k4_xboole_0(k1_tarski(X57),X58)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_zfmisc_1])])).
% 53.57/53.80  fof(c_0_11, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:((((r2_hidden(X11,X8)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9))&(r2_hidden(X11,X9)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9)))&(~r2_hidden(X12,X8)|~r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k3_xboole_0(X8,X9)))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|(~r2_hidden(esk1_3(X13,X14,X15),X13)|~r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k3_xboole_0(X13,X14))&((r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))&(r2_hidden(esk1_3(X13,X14,X15),X14)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 53.57/53.80  cnf(c_0_12, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_9])).
% 53.57/53.80  cnf(c_0_13, plain, (k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 53.57/53.80  cnf(c_0_14, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 53.57/53.80  cnf(c_0_15, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 53.57/53.80  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_14])).
% 53.57/53.80  cnf(c_0_17, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0|~r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),X2)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 53.57/53.80  fof(c_0_18, plain, ![X54, X55, X56]:((r2_hidden(X56,X55)|k3_xboole_0(k2_tarski(X54,X56),X55)=k1_tarski(X54)|~r2_hidden(X54,X55))&(X54!=X56|k3_xboole_0(k2_tarski(X54,X56),X55)=k1_tarski(X54)|~r2_hidden(X54,X55))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).
% 53.57/53.80  cnf(c_0_19, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_17, c_0_16])).
% 53.57/53.80  cnf(c_0_20, plain, (k3_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)|X1!=X2|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 53.57/53.80  cnf(c_0_21, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0|k3_xboole_0(X2,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_16])).
% 53.57/53.80  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 53.57/53.80  cnf(c_0_23, plain, (k3_xboole_0(k2_tarski(X1,X1),X2)=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_20])).
% 53.57/53.80  cnf(c_0_24, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(ef,[status(thm)],[c_0_21])).
% 53.57/53.80  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_22])).
% 53.57/53.80  cnf(c_0_26, plain, (k1_tarski(X1)=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 53.57/53.80  cnf(c_0_27, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 53.57/53.80  cnf(c_0_28, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 53.57/53.80  fof(c_0_29, plain, ![X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X28,X27)|X28=X26|X27!=k1_tarski(X26))&(X29!=X26|r2_hidden(X29,X27)|X27!=k1_tarski(X26)))&((~r2_hidden(esk3_2(X30,X31),X31)|esk3_2(X30,X31)!=X30|X31=k1_tarski(X30))&(r2_hidden(esk3_2(X30,X31),X31)|esk3_2(X30,X31)=X30|X31=k1_tarski(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 53.57/53.80  cnf(c_0_30, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0|~r2_hidden(X2,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_26]), c_0_27])).
% 53.57/53.80  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_28])).
% 53.57/53.80  cnf(c_0_32, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 53.57/53.80  cnf(c_0_33, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0|k4_xboole_0(k1_xboole_0,X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 53.57/53.80  cnf(c_0_34, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 53.57/53.80  cnf(c_0_35, plain, (r2_hidden(X1,k2_tarski(X2,X2))|~r2_hidden(X1,k1_tarski(X2))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 53.57/53.80  cnf(c_0_36, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).
% 53.57/53.80  cnf(c_0_37, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(ef,[status(thm)],[c_0_33])).
% 53.57/53.80  cnf(c_0_38, plain, (k3_xboole_0(X1,X2)=X2|~r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_16]), c_0_16])).
% 53.57/53.80  cnf(c_0_39, plain, (r2_hidden(X1,k2_tarski(X1,X1))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 53.57/53.80  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 53.57/53.80  cnf(c_0_41, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 53.57/53.80  cnf(c_0_42, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_37]), c_0_27])).
% 53.57/53.80  cnf(c_0_43, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 53.57/53.80  cnf(c_0_44, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_38, c_0_16])).
% 53.57/53.80  cnf(c_0_45, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_39, c_0_36])).
% 53.57/53.80  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_40])).
% 53.57/53.80  cnf(c_0_47, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_41])).
% 53.57/53.80  cnf(c_0_48, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 53.57/53.80  cnf(c_0_49, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 53.57/53.80  cnf(c_0_50, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_44]), c_0_45])])).
% 53.57/53.80  cnf(c_0_51, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,X3)|r2_hidden(esk1_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_46, c_0_16])).
% 53.57/53.80  cnf(c_0_52, plain, (esk1_3(k1_tarski(X1),X2,k1_xboole_0)=X1|k3_xboole_0(k1_tarski(X1),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 53.57/53.80  cnf(c_0_53, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_49])).
% 53.57/53.80  cnf(c_0_54, plain, (k3_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_50])).
% 53.57/53.80  cnf(c_0_55, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_38, c_0_51])).
% 53.57/53.80  cnf(c_0_56, plain, (k3_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|r2_hidden(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_52]), c_0_42])).
% 53.57/53.80  cnf(c_0_57, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(X2,X3)|r2_hidden(esk1_3(X1,k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_53, c_0_16])).
% 53.57/53.80  cnf(c_0_58, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 53.57/53.80  cnf(c_0_59, plain, (k3_xboole_0(X1,k1_tarski(X2))=k1_tarski(X2)|~r2_hidden(X2,k3_xboole_0(X1,k1_tarski(X2)))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 53.57/53.80  cnf(c_0_60, plain, (k3_xboole_0(X1,k1_tarski(X2))=k1_xboole_0|r2_hidden(X2,k3_xboole_0(X1,k1_tarski(X2)))), inference(spm,[status(thm)],[c_0_56, c_0_55])).
% 53.57/53.80  cnf(c_0_61, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_57])).
% 53.57/53.80  cnf(c_0_62, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_58])).
% 53.57/53.80  fof(c_0_63, plain, ![X33, X34, X35, X36, X39, X40, X41, X42, X43, X44, X46, X47]:(((((r2_hidden(esk4_4(X33,X34,X35,X36),X33)|~r2_hidden(X36,X35)|X35!=k2_zfmisc_1(X33,X34))&(r2_hidden(esk5_4(X33,X34,X35,X36),X34)|~r2_hidden(X36,X35)|X35!=k2_zfmisc_1(X33,X34)))&(X36=k4_tarski(esk4_4(X33,X34,X35,X36),esk5_4(X33,X34,X35,X36))|~r2_hidden(X36,X35)|X35!=k2_zfmisc_1(X33,X34)))&(~r2_hidden(X40,X33)|~r2_hidden(X41,X34)|X39!=k4_tarski(X40,X41)|r2_hidden(X39,X35)|X35!=k2_zfmisc_1(X33,X34)))&((~r2_hidden(esk6_3(X42,X43,X44),X44)|(~r2_hidden(X46,X42)|~r2_hidden(X47,X43)|esk6_3(X42,X43,X44)!=k4_tarski(X46,X47))|X44=k2_zfmisc_1(X42,X43))&(((r2_hidden(esk7_3(X42,X43,X44),X42)|r2_hidden(esk6_3(X42,X43,X44),X44)|X44=k2_zfmisc_1(X42,X43))&(r2_hidden(esk8_3(X42,X43,X44),X43)|r2_hidden(esk6_3(X42,X43,X44),X44)|X44=k2_zfmisc_1(X42,X43)))&(esk6_3(X42,X43,X44)=k4_tarski(esk7_3(X42,X43,X44),esk8_3(X42,X43,X44))|r2_hidden(esk6_3(X42,X43,X44),X44)|X44=k2_zfmisc_1(X42,X43))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 53.57/53.80  fof(c_0_64, negated_conjecture, ~(![X1, X2, X3, X4, X5]:~((r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))&![X6, X7]:~(((X1=k4_tarski(X6,X7)&r2_hidden(X6,k3_xboole_0(X2,X4)))&r2_hidden(X7,k3_xboole_0(X3,X5))))))), inference(assume_negation,[status(cth)],[t104_zfmisc_1])).
% 53.57/53.80  cnf(c_0_65, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 53.57/53.80  cnf(c_0_66, plain, (k3_xboole_0(X1,k1_tarski(X2))=k1_tarski(X2)|k3_xboole_0(X1,k1_tarski(X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 53.57/53.80  cnf(c_0_67, plain, (k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)|~r2_hidden(X1,k4_xboole_0(k1_tarski(X1),X2))), inference(spm,[status(thm)],[c_0_54, c_0_61])).
% 53.57/53.80  cnf(c_0_68, plain, (r2_hidden(X1,k4_xboole_0(k1_tarski(X1),X2))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_62, c_0_36])).
% 53.57/53.80  cnf(c_0_69, plain, (r2_hidden(esk5_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 53.57/53.80  fof(c_0_70, negated_conjecture, ![X64, X65]:(r2_hidden(esk9_0,k3_xboole_0(k2_zfmisc_1(esk10_0,esk11_0),k2_zfmisc_1(esk12_0,esk13_0)))&(esk9_0!=k4_tarski(X64,X65)|~r2_hidden(X64,k3_xboole_0(esk10_0,esk12_0))|~r2_hidden(X65,k3_xboole_0(esk11_0,esk13_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_64])])])])).
% 53.57/53.80  cnf(c_0_71, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_65])).
% 53.57/53.80  cnf(c_0_72, plain, (k3_xboole_0(X1,k1_tarski(X2))=k1_xboole_0|k1_tarski(X2)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_66])).
% 53.57/53.80  cnf(c_0_73, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 53.57/53.80  cnf(c_0_74, plain, (k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 53.57/53.80  cnf(c_0_75, plain, (r2_hidden(X1,X2)|k3_xboole_0(k2_tarski(X3,X1),X2)=k1_tarski(X3)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 53.57/53.80  cnf(c_0_76, plain, (r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_69])).
% 53.57/53.80  cnf(c_0_77, negated_conjecture, (r2_hidden(esk9_0,k3_xboole_0(k2_zfmisc_1(esk10_0,esk11_0),k2_zfmisc_1(esk12_0,esk13_0)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 53.57/53.80  cnf(c_0_78, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_28]), c_0_37])).
% 53.57/53.80  cnf(c_0_79, plain, (k1_tarski(X1)!=k1_xboole_0|~r2_hidden(X2,k1_tarski(X1))|~r2_hidden(X2,X3)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_42])).
% 53.57/53.80  cnf(c_0_80, plain, (r2_hidden(X1,X2)|k1_tarski(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 53.57/53.80  cnf(c_0_81, plain, (k3_xboole_0(k2_tarski(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X4),X2)=k1_tarski(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3))|r2_hidden(X4,X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 53.57/53.80  cnf(c_0_82, negated_conjecture, (r2_hidden(esk9_0,k2_zfmisc_1(esk12_0,esk13_0))), inference(spm,[status(thm)],[c_0_46, c_0_77])).
% 53.57/53.80  cnf(c_0_83, plain, (esk2_3(k1_xboole_0,X1,k1_tarski(X2))=X2|k1_tarski(X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_78])).
% 53.57/53.80  cnf(c_0_84, plain, (k1_tarski(X1)!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_36]), c_0_80])).
% 53.57/53.80  cnf(c_0_85, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 53.57/53.80  fof(c_0_86, plain, ![X50, X51, X52, X53]:(((r2_hidden(X50,X52)|~r2_hidden(k4_tarski(X50,X51),k2_zfmisc_1(X52,X53)))&(r2_hidden(X51,X53)|~r2_hidden(k4_tarski(X50,X51),k2_zfmisc_1(X52,X53))))&(~r2_hidden(X50,X52)|~r2_hidden(X51,X53)|r2_hidden(k4_tarski(X50,X51),k2_zfmisc_1(X52,X53)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 53.57/53.80  cnf(c_0_87, plain, (X1=k4_tarski(esk4_4(X2,X3,X4,X1),esk5_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k2_zfmisc_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 53.57/53.80  cnf(c_0_88, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,X3,k3_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_46, c_0_78])).
% 53.57/53.80  cnf(c_0_89, negated_conjecture, (k3_xboole_0(k2_tarski(esk5_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),X1),esk13_0)=k1_tarski(esk5_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0))|r2_hidden(X1,esk13_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 53.57/53.80  cnf(c_0_90, plain, (esk2_3(k1_xboole_0,X1,k1_tarski(X2))=X2), inference(sr,[status(thm)],[c_0_83, c_0_84])).
% 53.57/53.80  cnf(c_0_91, negated_conjecture, (r2_hidden(esk9_0,k2_zfmisc_1(esk10_0,esk11_0))), inference(spm,[status(thm)],[c_0_25, c_0_77])).
% 53.57/53.80  cnf(c_0_92, plain, (r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_85])).
% 53.57/53.80  cnf(c_0_93, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 53.57/53.80  cnf(c_0_94, plain, (k4_tarski(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3))=X3|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_87])).
% 53.57/53.80  cnf(c_0_95, negated_conjecture, (r2_hidden(esk5_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),esk13_0)|r2_hidden(X1,esk13_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90]), c_0_84])).
% 53.57/53.80  cnf(c_0_96, negated_conjecture, (k3_xboole_0(k2_tarski(esk5_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0),X1),esk11_0)=k1_tarski(esk5_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0))|r2_hidden(X1,esk11_0)), inference(spm,[status(thm)],[c_0_81, c_0_91])).
% 53.57/53.80  cnf(c_0_97, plain, (esk4_4(k1_tarski(X1),X2,k2_zfmisc_1(k1_tarski(X1),X2),X3)=X1|~r2_hidden(X3,k2_zfmisc_1(k1_tarski(X1),X2))), inference(spm,[status(thm)],[c_0_47, c_0_92])).
% 53.57/53.80  cnf(c_0_98, plain, (r2_hidden(X1,k2_zfmisc_1(X2,X3))|~r2_hidden(esk5_4(X4,X5,k2_zfmisc_1(X4,X5),X1),X3)|~r2_hidden(esk4_4(X4,X5,k2_zfmisc_1(X4,X5),X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X4,X5))), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 53.57/53.80  cnf(c_0_99, negated_conjecture, (r2_hidden(esk5_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),esk13_0)), inference(ef,[status(thm)],[c_0_95])).
% 53.57/53.80  cnf(c_0_100, negated_conjecture, (r2_hidden(esk5_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0),esk11_0)|r2_hidden(X1,esk11_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_96]), c_0_90]), c_0_84])).
% 53.57/53.80  cnf(c_0_101, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 53.57/53.80  cnf(c_0_102, plain, (k4_tarski(X1,esk5_4(k1_tarski(X1),X2,k2_zfmisc_1(k1_tarski(X1),X2),X3))=X3|~r2_hidden(X3,k2_zfmisc_1(k1_tarski(X1),X2))), inference(spm,[status(thm)],[c_0_94, c_0_97])).
% 53.57/53.80  cnf(c_0_103, negated_conjecture, (r2_hidden(esk9_0,k2_zfmisc_1(X1,esk13_0))|~r2_hidden(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_82])])).
% 53.57/53.80  cnf(c_0_104, negated_conjecture, (r2_hidden(esk5_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0),esk11_0)), inference(ef,[status(thm)],[c_0_100])).
% 53.57/53.80  cnf(c_0_105, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k2_zfmisc_1(k1_tarski(X1),X4))|~r2_hidden(X3,k2_zfmisc_1(X2,X5))), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 53.57/53.80  cnf(c_0_106, negated_conjecture, (r2_hidden(esk9_0,k2_zfmisc_1(k1_tarski(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0)),esk13_0))), inference(spm,[status(thm)],[c_0_103, c_0_36])).
% 53.57/53.80  cnf(c_0_107, negated_conjecture, (r2_hidden(esk9_0,k2_zfmisc_1(X1,esk11_0))|~r2_hidden(esk4_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_104]), c_0_91])])).
% 53.57/53.80  cnf(c_0_108, negated_conjecture, (esk9_0!=k4_tarski(X1,X2)|~r2_hidden(X1,k3_xboole_0(esk10_0,esk12_0))|~r2_hidden(X2,k3_xboole_0(esk11_0,esk13_0))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 53.57/53.80  cnf(c_0_109, plain, (k3_xboole_0(k2_tarski(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X4),X1)=k1_tarski(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3))|r2_hidden(X4,X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_75, c_0_92])).
% 53.57/53.80  cnf(c_0_110, negated_conjecture, (r2_hidden(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),X1)|~r2_hidden(esk9_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 53.57/53.80  cnf(c_0_111, negated_conjecture, (r2_hidden(esk9_0,k2_zfmisc_1(k1_tarski(esk4_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0)),esk11_0))), inference(spm,[status(thm)],[c_0_107, c_0_36])).
% 53.57/53.80  cnf(c_0_112, negated_conjecture, (k4_tarski(X1,X2)!=esk9_0|~r2_hidden(X1,k3_xboole_0(esk10_0,esk12_0))|~r2_hidden(X2,esk13_0)|~r2_hidden(X2,esk11_0)), inference(spm,[status(thm)],[c_0_108, c_0_71])).
% 53.57/53.80  cnf(c_0_113, negated_conjecture, (k3_xboole_0(k2_tarski(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),X1),esk12_0)=k1_tarski(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0))|r2_hidden(X1,esk12_0)), inference(spm,[status(thm)],[c_0_109, c_0_82])).
% 53.57/53.80  cnf(c_0_114, negated_conjecture, (r2_hidden(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),k1_tarski(esk4_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0)))), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 53.57/53.80  cnf(c_0_115, negated_conjecture, (k4_tarski(X1,X2)!=esk9_0|~r2_hidden(X2,esk13_0)|~r2_hidden(X2,esk11_0)|~r2_hidden(X1,esk12_0)|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_112, c_0_71])).
% 53.57/53.80  cnf(c_0_116, negated_conjecture, (r2_hidden(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),esk12_0)|r2_hidden(X1,esk12_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_113]), c_0_90]), c_0_84])).
% 53.57/53.80  cnf(c_0_117, negated_conjecture, (esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0)=esk4_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0)), inference(spm,[status(thm)],[c_0_47, c_0_114])).
% 53.57/53.80  cnf(c_0_118, negated_conjecture, (r2_hidden(esk4_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0),X1)|~r2_hidden(esk9_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_105, c_0_111])).
% 53.57/53.80  cnf(c_0_119, negated_conjecture, (~r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),esk9_0),esk13_0)|~r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),esk9_0),esk11_0)|~r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),esk9_0),esk12_0)|~r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),esk9_0),esk10_0)|~r2_hidden(esk9_0,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_94])])).
% 53.57/53.80  cnf(c_0_120, negated_conjecture, (r2_hidden(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),esk12_0)), inference(ef,[status(thm)],[c_0_116])).
% 53.57/53.80  cnf(c_0_121, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 53.57/53.80  cnf(c_0_122, negated_conjecture, (k4_tarski(esk4_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0),esk5_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0))=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_117]), c_0_82])])).
% 53.57/53.80  cnf(c_0_123, negated_conjecture, (r2_hidden(esk4_4(esk10_0,esk11_0,k2_zfmisc_1(esk10_0,esk11_0),esk9_0),esk12_0)), inference(spm,[status(thm)],[c_0_118, c_0_82])).
% 53.57/53.80  cnf(c_0_124, negated_conjecture, (~r2_hidden(esk5_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),esk11_0)|~r2_hidden(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_99]), c_0_120]), c_0_82])])).
% 53.57/53.80  cnf(c_0_125, negated_conjecture, (r2_hidden(esk4_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),esk10_0)), inference(spm,[status(thm)],[c_0_110, c_0_91])).
% 53.57/53.80  cnf(c_0_126, negated_conjecture, (r2_hidden(esk5_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),X1)|~r2_hidden(esk9_0,k2_zfmisc_1(X2,X1))), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 53.57/53.80  cnf(c_0_127, negated_conjecture, (r2_hidden(esk9_0,k2_zfmisc_1(esk12_0,esk11_0))), inference(spm,[status(thm)],[c_0_107, c_0_123])).
% 53.57/53.80  cnf(c_0_128, negated_conjecture, (~r2_hidden(esk5_4(esk12_0,esk13_0,k2_zfmisc_1(esk12_0,esk13_0),esk9_0),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_125])])).
% 53.57/53.80  cnf(c_0_129, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_128]), ['proof']).
% 53.57/53.80  # SZS output end CNFRefutation
% 53.57/53.80  # Proof object total steps             : 130
% 53.57/53.80  # Proof object clause steps            : 113
% 53.57/53.80  # Proof object formula steps           : 17
% 53.57/53.80  # Proof object conjectures             : 35
% 53.57/53.80  # Proof object clause conjectures      : 32
% 53.57/53.80  # Proof object formula conjectures     : 3
% 53.57/53.80  # Proof object initial clauses used    : 24
% 53.57/53.80  # Proof object initial formulas used   : 8
% 53.57/53.80  # Proof object generating inferences   : 74
% 53.57/53.80  # Proof object simplifying inferences  : 43
% 53.57/53.80  # Training examples: 0 positive, 0 negative
% 53.57/53.80  # Parsed axioms                        : 8
% 53.57/53.80  # Removed by relevancy pruning/SinE    : 0
% 53.57/53.80  # Initial clauses                      : 33
% 53.57/53.80  # Removed in clause preprocessing      : 0
% 53.57/53.80  # Initial clauses in saturation        : 33
% 53.57/53.80  # Processed clauses                    : 56775
% 53.57/53.80  # ...of these trivial                  : 443
% 53.57/53.80  # ...subsumed                          : 50308
% 53.57/53.80  # ...remaining for further processing  : 6024
% 53.57/53.80  # Other redundant clauses eliminated   : 324
% 53.57/53.80  # Clauses deleted for lack of memory   : 60370
% 53.57/53.80  # Backward-subsumed                    : 201
% 53.57/53.80  # Backward-rewritten                   : 371
% 53.57/53.80  # Generated clauses                    : 3657346
% 53.57/53.80  # ...of the previous two non-trivial   : 3525803
% 53.57/53.80  # Contextual simplify-reflections      : 12
% 53.57/53.80  # Paramodulations                      : 3655389
% 53.57/53.80  # Factorizations                       : 1626
% 53.57/53.80  # Equation resolutions                 : 324
% 53.57/53.80  # Propositional unsat checks           : 1
% 53.57/53.80  #    Propositional check models        : 0
% 53.57/53.80  #    Propositional check unsatisfiable : 0
% 53.57/53.80  #    Propositional clauses             : 0
% 53.57/53.80  #    Propositional clauses after purity: 0
% 53.57/53.80  #    Propositional unsat core size     : 0
% 53.57/53.80  #    Propositional preprocessing time  : 0.000
% 53.57/53.80  #    Propositional encoding time       : 2.891
% 53.57/53.80  #    Propositional solver time         : 0.959
% 53.57/53.80  #    Success case prop preproc time    : 0.000
% 53.57/53.80  #    Success case prop encoding time   : 0.000
% 53.57/53.80  #    Success case prop solver time     : 0.000
% 53.57/53.80  # Current number of processed clauses  : 5398
% 53.57/53.80  #    Positive orientable unit clauses  : 248
% 53.57/53.80  #    Positive unorientable unit clauses: 0
% 53.57/53.80  #    Negative unit clauses             : 77
% 53.57/53.80  #    Non-unit-clauses                  : 5073
% 53.57/53.80  # Current number of unprocessed clauses: 1643612
% 53.57/53.80  # ...number of literals in the above   : 8482000
% 53.57/53.80  # Current number of archived formulas  : 0
% 53.57/53.80  # Current number of archived clauses   : 613
% 53.57/53.80  # Clause-clause subsumption calls (NU) : 3783246
% 53.57/53.80  # Rec. Clause-clause subsumption calls : 1237076
% 53.57/53.80  # Non-unit clause-clause subsumptions  : 15625
% 53.57/53.80  # Unit Clause-clause subsumption calls : 123533
% 53.57/53.80  # Rewrite failures with RHS unbound    : 0
% 53.57/53.80  # BW rewrite match attempts            : 3055
% 53.57/53.80  # BW rewrite match successes           : 151
% 53.57/53.80  # Condensation attempts                : 0
% 53.57/53.80  # Condensation successes               : 0
% 53.57/53.80  # Termbank termtop insertions          : 132742038
% 53.61/53.89  
% 53.61/53.89  # -------------------------------------------------
% 53.61/53.89  # User time                : 52.363 s
% 53.61/53.89  # System time              : 1.137 s
% 53.61/53.89  # Total time               : 53.500 s
% 53.61/53.89  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
