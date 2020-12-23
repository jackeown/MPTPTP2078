%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:30 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   73 (1143 expanded)
%              Number of clauses        :   52 ( 546 expanded)
%              Number of leaves         :   10 ( 295 expanded)
%              Depth                    :   19
%              Number of atoms          :  173 (3248 expanded)
%              Number of equality atoms :   69 ( 954 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t103_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_xboole_1)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t104_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ~ ( r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))
        & ! [X6,X7] :
            ~ ( X1 = k4_tarski(X6,X7)
              & r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X7,k3_xboole_0(X3,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_zfmisc_1)).

fof(c_0_10,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( r2_hidden(X17,X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X14)
        | r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X20)
        | X21 = k4_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k4_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X20)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k4_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_12,plain,(
    ! [X25,X26] : k4_xboole_0(X25,X26) = k5_xboole_0(X25,k3_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,plain,(
    ! [X29,X30] :
      ( ~ r1_tarski(X29,X30)
      | k3_xboole_0(X29,X30) = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_20,plain,(
    ! [X31] : k5_xboole_0(X31,X31) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_21,plain,(
    ! [X27,X28] : r1_xboole_0(k3_xboole_0(X27,X28),k5_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t103_xboole_1])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_28,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

fof(c_0_29,plain,(
    ! [X39,X40,X41,X42] :
      ( ( r2_hidden(X39,X41)
        | ~ r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)) )
      & ( r2_hidden(X40,X42)
        | ~ r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)) )
      & ( ~ r2_hidden(X39,X41)
        | ~ r2_hidden(X40,X42)
        | r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

fof(c_0_31,plain,(
    ! [X23,X24] :
      ( ( ~ r1_xboole_0(X23,X24)
        | k3_xboole_0(X23,X24) = k1_xboole_0 )
      & ( k3_xboole_0(X23,X24) != k1_xboole_0
        | r1_xboole_0(X23,X24) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_32,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_33,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_25]),c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,negated_conjecture,
    ( ( esk5_0 != k1_xboole_0
      | k2_zfmisc_1(esk5_0,esk6_0) != k1_xboole_0 )
    & ( esk6_0 != k1_xboole_0
      | k2_zfmisc_1(esk5_0,esk6_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk5_0,esk6_0) = k1_xboole_0
      | esk5_0 = k1_xboole_0
      | esk6_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_24])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(X1,X2) != k1_xboole_0
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X2,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_33]),c_0_33])).

cnf(c_0_42,plain,
    ( X1 != k5_xboole_0(X2,k1_xboole_0)
    | ~ r2_hidden(X3,k1_xboole_0)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ r2_hidden(X2,esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_15])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_xboole_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | r1_tarski(esk6_0,X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_15])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_25])).

cnf(c_0_47,negated_conjecture,
    ( k3_xboole_0(esk6_0,X1) = esk6_0
    | r1_tarski(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_45])).

fof(c_0_48,plain,(
    ! [X32,X33,X34,X35,X36] :
      ( ( X32 = k4_tarski(esk3_5(X32,X33,X34,X35,X36),esk4_5(X32,X33,X34,X35,X36))
        | ~ r2_hidden(X32,k3_xboole_0(k2_zfmisc_1(X33,X34),k2_zfmisc_1(X35,X36))) )
      & ( r2_hidden(esk3_5(X32,X33,X34,X35,X36),k3_xboole_0(X33,X35))
        | ~ r2_hidden(X32,k3_xboole_0(k2_zfmisc_1(X33,X34),k2_zfmisc_1(X35,X36))) )
      & ( r2_hidden(esk4_5(X32,X33,X34,X35,X36),k3_xboole_0(X34,X36))
        | ~ r2_hidden(X32,k3_xboole_0(k2_zfmisc_1(X33,X34),k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t104_zfmisc_1])])])])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_47])).

cnf(c_0_51,plain,
    ( r2_hidden(esk4_5(X1,X2,X3,X4,X5),k3_xboole_0(X3,X5))
    | ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(esk5_0,X1) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_50])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,k1_xboole_0),k2_zfmisc_1(X3,X4))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_46])).

cnf(c_0_55,plain,
    ( r2_hidden(esk3_5(X1,X2,X3,X4,X5),k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_xboole_0(esk5_0,k5_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_53])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_24])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X2),k2_zfmisc_1(X3,X4))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_52]),c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(esk5_0,k5_xboole_0(esk5_0,X1)) = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_56])).

cnf(c_0_60,plain,
    ( r1_tarski(k2_zfmisc_1(X1,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_15])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_24])).

cnf(c_0_62,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | k2_zfmisc_1(esk5_0,esk6_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_63,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_59])).

cnf(c_0_64,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,k1_xboole_0),X2) = k2_zfmisc_1(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_60])).

cnf(c_0_65,plain,
    ( r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_15])).

cnf(c_0_66,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | k2_zfmisc_1(esk5_0,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_64])).

cnf(c_0_68,plain,
    ( k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X1),X2) = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | k2_zfmisc_1(esk5_0,esk6_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_70,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_71,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_70])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:10:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.12/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.016 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.36  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.12/0.36  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.12/0.36  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.12/0.36  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.12/0.36  fof(t103_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_xboole_1)).
% 0.12/0.36  fof(t106_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 0.12/0.36  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.12/0.36  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.12/0.36  fof(t104_zfmisc_1, axiom, ![X1, X2, X3, X4, X5]:~((r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))&![X6, X7]:~(((X1=k4_tarski(X6,X7)&r2_hidden(X6,k3_xboole_0(X2,X4)))&r2_hidden(X7,k3_xboole_0(X3,X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_zfmisc_1)).
% 0.12/0.36  fof(c_0_10, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.36  fof(c_0_11, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:((((r2_hidden(X17,X14)|~r2_hidden(X17,X16)|X16!=k4_xboole_0(X14,X15))&(~r2_hidden(X17,X15)|~r2_hidden(X17,X16)|X16!=k4_xboole_0(X14,X15)))&(~r2_hidden(X18,X14)|r2_hidden(X18,X15)|r2_hidden(X18,X16)|X16!=k4_xboole_0(X14,X15)))&((~r2_hidden(esk2_3(X19,X20,X21),X21)|(~r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X20))|X21=k4_xboole_0(X19,X20))&((r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k4_xboole_0(X19,X20))&(~r2_hidden(esk2_3(X19,X20,X21),X20)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k4_xboole_0(X19,X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.12/0.36  fof(c_0_12, plain, ![X25, X26]:k4_xboole_0(X25,X26)=k5_xboole_0(X25,k3_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.12/0.36  fof(c_0_13, plain, ![X29, X30]:(~r1_tarski(X29,X30)|k3_xboole_0(X29,X30)=X29), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.12/0.36  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.36  cnf(c_0_15, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.36  cnf(c_0_16, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.36  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.36  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.36  cnf(c_0_19, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.36  fof(c_0_20, plain, ![X31]:k5_xboole_0(X31,X31)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.12/0.36  fof(c_0_21, plain, ![X27, X28]:r1_xboole_0(k3_xboole_0(X27,X28),k5_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t103_xboole_1])).
% 0.12/0.36  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.36  cnf(c_0_23, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.36  cnf(c_0_24, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.36  cnf(c_0_25, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.36  cnf(c_0_26, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.36  cnf(c_0_27, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_22, c_0_17])).
% 0.12/0.36  cnf(c_0_28, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)|~r2_hidden(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.12/0.36  fof(c_0_29, plain, ![X39, X40, X41, X42]:(((r2_hidden(X39,X41)|~r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)))&(r2_hidden(X40,X42)|~r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42))))&(~r2_hidden(X39,X41)|~r2_hidden(X40,X42)|r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).
% 0.12/0.36  fof(c_0_30, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.12/0.36  fof(c_0_31, plain, ![X23, X24]:((~r1_xboole_0(X23,X24)|k3_xboole_0(X23,X24)=k1_xboole_0)&(k3_xboole_0(X23,X24)!=k1_xboole_0|r1_xboole_0(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.12/0.36  cnf(c_0_32, plain, (r1_xboole_0(k3_xboole_0(X1,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_26, c_0_25])).
% 0.12/0.36  cnf(c_0_33, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_24]), c_0_25]), c_0_28])).
% 0.12/0.36  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.36  fof(c_0_35, negated_conjecture, (((esk5_0!=k1_xboole_0|k2_zfmisc_1(esk5_0,esk6_0)!=k1_xboole_0)&(esk6_0!=k1_xboole_0|k2_zfmisc_1(esk5_0,esk6_0)!=k1_xboole_0))&(k2_zfmisc_1(esk5_0,esk6_0)=k1_xboole_0|(esk5_0=k1_xboole_0|esk6_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])])).
% 0.12/0.36  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.36  cnf(c_0_37, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_32, c_0_24])).
% 0.12/0.36  cnf(c_0_38, plain, (k2_zfmisc_1(X1,X2)!=k1_xboole_0|~r2_hidden(X3,X2)|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.36  cnf(c_0_39, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.36  cnf(c_0_40, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.12/0.36  cnf(c_0_41, negated_conjecture, (~r2_hidden(X1,esk6_0)|~r2_hidden(X2,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_33]), c_0_33])).
% 0.12/0.36  cnf(c_0_42, plain, (X1!=k5_xboole_0(X2,k1_xboole_0)|~r2_hidden(X3,k1_xboole_0)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_23, c_0_40])).
% 0.12/0.36  cnf(c_0_43, negated_conjecture, (r1_tarski(esk6_0,X1)|~r2_hidden(X2,esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_15])).
% 0.12/0.36  cnf(c_0_44, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_xboole_0))|~r2_hidden(X1,k1_xboole_0)), inference(er,[status(thm)],[c_0_42])).
% 0.12/0.36  cnf(c_0_45, negated_conjecture, (r1_tarski(esk5_0,X1)|r1_tarski(esk6_0,X2)), inference(spm,[status(thm)],[c_0_43, c_0_15])).
% 0.12/0.36  cnf(c_0_46, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_25])).
% 0.12/0.36  cnf(c_0_47, negated_conjecture, (k3_xboole_0(esk6_0,X1)=esk6_0|r1_tarski(esk5_0,X2)), inference(spm,[status(thm)],[c_0_18, c_0_45])).
% 0.12/0.36  fof(c_0_48, plain, ![X32, X33, X34, X35, X36]:(((X32=k4_tarski(esk3_5(X32,X33,X34,X35,X36),esk4_5(X32,X33,X34,X35,X36))|~r2_hidden(X32,k3_xboole_0(k2_zfmisc_1(X33,X34),k2_zfmisc_1(X35,X36))))&(r2_hidden(esk3_5(X32,X33,X34,X35,X36),k3_xboole_0(X33,X35))|~r2_hidden(X32,k3_xboole_0(k2_zfmisc_1(X33,X34),k2_zfmisc_1(X35,X36)))))&(r2_hidden(esk4_5(X32,X33,X34,X35,X36),k3_xboole_0(X34,X36))|~r2_hidden(X32,k3_xboole_0(k2_zfmisc_1(X33,X34),k2_zfmisc_1(X35,X36))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t104_zfmisc_1])])])])).
% 0.12/0.36  cnf(c_0_49, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_46, c_0_15])).
% 0.12/0.36  cnf(c_0_50, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_47])).
% 0.12/0.36  cnf(c_0_51, plain, (r2_hidden(esk4_5(X1,X2,X3,X4,X5),k3_xboole_0(X3,X5))|~r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.36  cnf(c_0_52, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_49])).
% 0.12/0.36  cnf(c_0_53, negated_conjecture, (k3_xboole_0(esk5_0,X1)=esk5_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_50])).
% 0.12/0.36  cnf(c_0_54, plain, (~r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,k1_xboole_0),k2_zfmisc_1(X3,X4)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_46])).
% 0.12/0.36  cnf(c_0_55, plain, (r2_hidden(esk3_5(X1,X2,X3,X4,X5),k3_xboole_0(X2,X4))|~r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.36  cnf(c_0_56, negated_conjecture, (esk6_0=k1_xboole_0|r1_xboole_0(esk5_0,k5_xboole_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_26, c_0_53])).
% 0.12/0.36  cnf(c_0_57, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_54, c_0_24])).
% 0.12/0.36  cnf(c_0_58, plain, (~r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X2),k2_zfmisc_1(X3,X4)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_52]), c_0_46])).
% 0.12/0.36  cnf(c_0_59, negated_conjecture, (k3_xboole_0(esk5_0,k5_xboole_0(esk5_0,X1))=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_56])).
% 0.12/0.36  cnf(c_0_60, plain, (r1_tarski(k2_zfmisc_1(X1,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_57, c_0_15])).
% 0.12/0.36  cnf(c_0_61, plain, (~r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_58, c_0_24])).
% 0.12/0.36  cnf(c_0_62, negated_conjecture, (esk6_0!=k1_xboole_0|k2_zfmisc_1(esk5_0,esk6_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.36  cnf(c_0_63, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_59])).
% 0.12/0.36  cnf(c_0_64, plain, (k3_xboole_0(k2_zfmisc_1(X1,k1_xboole_0),X2)=k2_zfmisc_1(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_60])).
% 0.12/0.36  cnf(c_0_65, plain, (r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_61, c_0_15])).
% 0.12/0.36  cnf(c_0_66, negated_conjecture, (esk5_0=k1_xboole_0|k2_zfmisc_1(esk5_0,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.12/0.36  cnf(c_0_67, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_64])).
% 0.12/0.36  cnf(c_0_68, plain, (k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X1),X2)=k2_zfmisc_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_65])).
% 0.12/0.37  cnf(c_0_69, negated_conjecture, (esk5_0!=k1_xboole_0|k2_zfmisc_1(esk5_0,esk6_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.37  cnf(c_0_70, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67])])).
% 0.12/0.37  cnf(c_0_71, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_68])).
% 0.12/0.37  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_70])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 73
% 0.12/0.37  # Proof object clause steps            : 52
% 0.12/0.37  # Proof object formula steps           : 21
% 0.12/0.37  # Proof object conjectures             : 18
% 0.12/0.37  # Proof object clause conjectures      : 15
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 15
% 0.12/0.37  # Proof object initial formulas used   : 10
% 0.12/0.37  # Proof object generating inferences   : 32
% 0.12/0.37  # Proof object simplifying inferences  : 16
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 10
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 24
% 0.12/0.37  # Removed in clause preprocessing      : 1
% 0.12/0.37  # Initial clauses in saturation        : 23
% 0.12/0.37  # Processed clauses                    : 134
% 0.12/0.37  # ...of these trivial                  : 3
% 0.12/0.37  # ...subsumed                          : 38
% 0.12/0.37  # ...remaining for further processing  : 93
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 2
% 0.12/0.37  # Backward-rewritten                   : 29
% 0.12/0.37  # Generated clauses                    : 240
% 0.12/0.37  # ...of the previous two non-trivial   : 215
% 0.12/0.37  # Contextual simplify-reflections      : 3
% 0.12/0.37  # Paramodulations                      : 233
% 0.12/0.37  # Factorizations                       : 2
% 0.12/0.37  # Equation resolutions                 : 5
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 39
% 0.12/0.37  #    Positive orientable unit clauses  : 13
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 25
% 0.12/0.37  # Current number of unprocessed clauses: 116
% 0.12/0.37  # ...number of literals in the above   : 313
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 55
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 265
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 197
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 19
% 0.12/0.37  # Unit Clause-clause subsumption calls : 19
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 13
% 0.12/0.37  # BW rewrite match successes           : 11
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 4147
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.018 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.023 s
% 0.12/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
