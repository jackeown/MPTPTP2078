%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:26 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   67 (3572 expanded)
%              Number of clauses        :   52 (1819 expanded)
%              Number of leaves         :    7 ( 874 expanded)
%              Depth                    :   22
%              Number of atoms          :  203 (15610 expanded)
%              Number of equality atoms :   83 (3654 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_7,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_xboole_0(X13,X14) )
      & ( r2_hidden(esk2_2(X13,X14),X14)
        | r1_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_8,plain,(
    ! [X20] : r1_xboole_0(X20,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_9,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_10,plain,(
    ! [X19] : r1_tarski(k1_xboole_0,X19) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_16,plain,(
    ! [X21,X22,X23,X24,X27,X28,X29,X30,X31,X32,X34,X35] :
      ( ( r2_hidden(esk3_4(X21,X22,X23,X24),X21)
        | ~ r2_hidden(X24,X23)
        | X23 != k2_zfmisc_1(X21,X22) )
      & ( r2_hidden(esk4_4(X21,X22,X23,X24),X22)
        | ~ r2_hidden(X24,X23)
        | X23 != k2_zfmisc_1(X21,X22) )
      & ( X24 = k4_tarski(esk3_4(X21,X22,X23,X24),esk4_4(X21,X22,X23,X24))
        | ~ r2_hidden(X24,X23)
        | X23 != k2_zfmisc_1(X21,X22) )
      & ( ~ r2_hidden(X28,X21)
        | ~ r2_hidden(X29,X22)
        | X27 != k4_tarski(X28,X29)
        | r2_hidden(X27,X23)
        | X23 != k2_zfmisc_1(X21,X22) )
      & ( ~ r2_hidden(esk5_3(X30,X31,X32),X32)
        | ~ r2_hidden(X34,X30)
        | ~ r2_hidden(X35,X31)
        | esk5_3(X30,X31,X32) != k4_tarski(X34,X35)
        | X32 = k2_zfmisc_1(X30,X31) )
      & ( r2_hidden(esk6_3(X30,X31,X32),X30)
        | r2_hidden(esk5_3(X30,X31,X32),X32)
        | X32 = k2_zfmisc_1(X30,X31) )
      & ( r2_hidden(esk7_3(X30,X31,X32),X31)
        | r2_hidden(esk5_3(X30,X31,X32),X32)
        | X32 = k2_zfmisc_1(X30,X31) )
      & ( esk5_3(X30,X31,X32) = k4_tarski(esk6_3(X30,X31,X32),esk7_3(X30,X31,X32))
        | r2_hidden(esk5_3(X30,X31,X32),X32)
        | X32 = k2_zfmisc_1(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X38,X39,X40,X42,X43,X44,X45,X47] :
      ( ( r2_hidden(X40,esk8_3(X38,X39,X40))
        | ~ r2_hidden(X40,X39)
        | X39 != k3_tarski(X38) )
      & ( r2_hidden(esk8_3(X38,X39,X40),X38)
        | ~ r2_hidden(X40,X39)
        | X39 != k3_tarski(X38) )
      & ( ~ r2_hidden(X42,X43)
        | ~ r2_hidden(X43,X38)
        | r2_hidden(X42,X39)
        | X39 != k3_tarski(X38) )
      & ( ~ r2_hidden(esk9_2(X44,X45),X45)
        | ~ r2_hidden(esk9_2(X44,X45),X47)
        | ~ r2_hidden(X47,X44)
        | X45 = k3_tarski(X44) )
      & ( r2_hidden(esk9_2(X44,X45),esk10_2(X44,X45))
        | r2_hidden(esk9_2(X44,X45),X45)
        | X45 = k3_tarski(X44) )
      & ( r2_hidden(esk10_2(X44,X45),X44)
        | r2_hidden(esk9_2(X44,X45),X45)
        | X45 = k3_tarski(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_20,plain,
    ( X1 != k2_zfmisc_1(k1_xboole_0,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( r2_hidden(esk8_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_23,plain,
    ( X1 != k3_tarski(k1_xboole_0)
    | ~ r2_hidden(esk8_3(k1_xboole_0,X1,X2),X3)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_21])).

cnf(c_0_24,plain,
    ( X1 != k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_25,plain,
    ( X1 != k3_tarski(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_27,plain,
    ( X1 != k3_tarski(k1_xboole_0)
    | X2 != k3_tarski(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_21])).

cnf(c_0_28,plain,
    ( X1 != k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21])).

cnf(c_0_29,plain,
    ( X1 != k3_tarski(k3_tarski(k1_xboole_0))
    | ~ r2_hidden(X2,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)))) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_31,plain,
    ( r2_hidden(esk10_2(X1,X2),X1)
    | r2_hidden(esk9_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( X1 != k3_tarski(k3_tarski(k1_xboole_0))
    | X2 != k3_tarski(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_21])).

cnf(c_0_33,plain,
    ( X1 != k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_21])).

cnf(c_0_34,plain,
    ( X1 = k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)))
    | r2_hidden(esk9_2(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)),X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_31])).

cnf(c_0_35,plain,
    ( X1 != k3_tarski(k3_tarski(k3_tarski(k1_xboole_0)))
    | ~ r2_hidden(X2,X1) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))))) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_37,plain,
    ( k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_34])).

cnf(c_0_38,plain,
    ( X1 != k3_tarski(k3_tarski(k3_tarski(k1_xboole_0)))
    | X2 != k2_zfmisc_1(X1,X3)
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_18])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k3_tarski(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk9_2(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)),X1),X1) ),
    inference(rw,[status(thm)],[c_0_34,c_0_37])).

cnf(c_0_41,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_42,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

cnf(c_0_43,plain,
    ( X1 != k3_tarski(k3_tarski(k3_tarski(k1_xboole_0)))
    | ~ r2_hidden(X2,k2_zfmisc_1(X1,X3)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_40])).

cnf(c_0_46,plain,
    ( X1 != k3_tarski(k3_tarski(k1_xboole_0))
    | X2 != k2_zfmisc_1(X3,X1)
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_41])).

fof(c_0_47,negated_conjecture,
    ( ( esk11_0 != k1_xboole_0
      | k2_zfmisc_1(esk11_0,esk12_0) != k1_xboole_0 )
    & ( esk12_0 != k1_xboole_0
      | k2_zfmisc_1(esk11_0,esk12_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk11_0,esk12_0) = k1_xboole_0
      | esk11_0 = k1_xboole_0
      | esk12_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])])).

cnf(c_0_48,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k2_zfmisc_1(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_44]),c_0_44])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk9_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_45]),c_0_44])).

cnf(c_0_50,plain,
    ( X1 != k3_tarski(k3_tarski(k1_xboole_0))
    | ~ r2_hidden(X2,k2_zfmisc_1(X3,X1)) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( esk11_0 != k1_xboole_0
    | k2_zfmisc_1(esk11_0,esk12_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k2_zfmisc_1(X3,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_44]),c_0_44])).

cnf(c_0_54,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_55,negated_conjecture,
    ( k2_zfmisc_1(esk11_0,esk12_0) = k1_xboole_0
    | esk11_0 = k1_xboole_0
    | esk12_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( esk11_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( esk12_0 != k1_xboole_0
    | k2_zfmisc_1(esk11_0,esk12_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_49])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | X1 != k4_tarski(X4,X5)
    | ~ r2_hidden(X5,X3)
    | ~ r2_hidden(X4,X2) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k2_zfmisc_1(esk11_0,esk12_0) = k1_xboole_0
    | esk12_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( esk12_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( k2_zfmisc_1(esk11_0,esk12_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(X1,esk12_0)
    | ~ r2_hidden(X2,esk11_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_17])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_hidden(X1,esk11_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_49]),c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_49]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:25:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.52  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.19/0.52  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.52  #
% 0.19/0.52  # Preprocessing time       : 0.028 s
% 0.19/0.52  # Presaturation interreduction done
% 0.19/0.52  
% 0.19/0.52  # Proof found!
% 0.19/0.52  # SZS status Theorem
% 0.19/0.52  # SZS output start CNFRefutation
% 0.19/0.52  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.52  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.52  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.52  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.52  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.19/0.52  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 0.19/0.52  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.52  fof(c_0_7, plain, ![X13, X14, X16, X17, X18]:(((r2_hidden(esk2_2(X13,X14),X13)|r1_xboole_0(X13,X14))&(r2_hidden(esk2_2(X13,X14),X14)|r1_xboole_0(X13,X14)))&(~r2_hidden(X18,X16)|~r2_hidden(X18,X17)|~r1_xboole_0(X16,X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.52  fof(c_0_8, plain, ![X20]:r1_xboole_0(X20,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.52  fof(c_0_9, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.52  fof(c_0_10, plain, ![X19]:r1_tarski(k1_xboole_0,X19), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.52  cnf(c_0_11, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.52  cnf(c_0_12, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.52  cnf(c_0_13, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.52  cnf(c_0_14, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.52  cnf(c_0_15, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.52  fof(c_0_16, plain, ![X21, X22, X23, X24, X27, X28, X29, X30, X31, X32, X34, X35]:(((((r2_hidden(esk3_4(X21,X22,X23,X24),X21)|~r2_hidden(X24,X23)|X23!=k2_zfmisc_1(X21,X22))&(r2_hidden(esk4_4(X21,X22,X23,X24),X22)|~r2_hidden(X24,X23)|X23!=k2_zfmisc_1(X21,X22)))&(X24=k4_tarski(esk3_4(X21,X22,X23,X24),esk4_4(X21,X22,X23,X24))|~r2_hidden(X24,X23)|X23!=k2_zfmisc_1(X21,X22)))&(~r2_hidden(X28,X21)|~r2_hidden(X29,X22)|X27!=k4_tarski(X28,X29)|r2_hidden(X27,X23)|X23!=k2_zfmisc_1(X21,X22)))&((~r2_hidden(esk5_3(X30,X31,X32),X32)|(~r2_hidden(X34,X30)|~r2_hidden(X35,X31)|esk5_3(X30,X31,X32)!=k4_tarski(X34,X35))|X32=k2_zfmisc_1(X30,X31))&(((r2_hidden(esk6_3(X30,X31,X32),X30)|r2_hidden(esk5_3(X30,X31,X32),X32)|X32=k2_zfmisc_1(X30,X31))&(r2_hidden(esk7_3(X30,X31,X32),X31)|r2_hidden(esk5_3(X30,X31,X32),X32)|X32=k2_zfmisc_1(X30,X31)))&(esk5_3(X30,X31,X32)=k4_tarski(esk6_3(X30,X31,X32),esk7_3(X30,X31,X32))|r2_hidden(esk5_3(X30,X31,X32),X32)|X32=k2_zfmisc_1(X30,X31))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.19/0.52  cnf(c_0_17, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.19/0.52  cnf(c_0_18, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.52  fof(c_0_19, plain, ![X38, X39, X40, X42, X43, X44, X45, X47]:((((r2_hidden(X40,esk8_3(X38,X39,X40))|~r2_hidden(X40,X39)|X39!=k3_tarski(X38))&(r2_hidden(esk8_3(X38,X39,X40),X38)|~r2_hidden(X40,X39)|X39!=k3_tarski(X38)))&(~r2_hidden(X42,X43)|~r2_hidden(X43,X38)|r2_hidden(X42,X39)|X39!=k3_tarski(X38)))&((~r2_hidden(esk9_2(X44,X45),X45)|(~r2_hidden(esk9_2(X44,X45),X47)|~r2_hidden(X47,X44))|X45=k3_tarski(X44))&((r2_hidden(esk9_2(X44,X45),esk10_2(X44,X45))|r2_hidden(esk9_2(X44,X45),X45)|X45=k3_tarski(X44))&(r2_hidden(esk10_2(X44,X45),X44)|r2_hidden(esk9_2(X44,X45),X45)|X45=k3_tarski(X44))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.19/0.52  cnf(c_0_20, plain, (X1!=k2_zfmisc_1(k1_xboole_0,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.52  cnf(c_0_21, plain, (r2_hidden(esk8_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.52  cnf(c_0_22, plain, (~r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2))), inference(er,[status(thm)],[c_0_20])).
% 0.19/0.52  cnf(c_0_23, plain, (X1!=k3_tarski(k1_xboole_0)|~r2_hidden(esk8_3(k1_xboole_0,X1,X2),X3)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_15, c_0_21])).
% 0.19/0.52  cnf(c_0_24, plain, (X1!=k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.19/0.52  cnf(c_0_25, plain, (X1!=k3_tarski(k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 0.19/0.52  cnf(c_0_26, plain, (~r2_hidden(X1,k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)))), inference(er,[status(thm)],[c_0_24])).
% 0.19/0.52  cnf(c_0_27, plain, (X1!=k3_tarski(k1_xboole_0)|X2!=k3_tarski(X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_25, c_0_21])).
% 0.19/0.52  cnf(c_0_28, plain, (X1!=k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_26, c_0_21])).
% 0.19/0.52  cnf(c_0_29, plain, (X1!=k3_tarski(k3_tarski(k1_xboole_0))|~r2_hidden(X2,X1)), inference(er,[status(thm)],[c_0_27])).
% 0.19/0.52  cnf(c_0_30, plain, (~r2_hidden(X1,k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))))), inference(er,[status(thm)],[c_0_28])).
% 0.19/0.52  cnf(c_0_31, plain, (r2_hidden(esk10_2(X1,X2),X1)|r2_hidden(esk9_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.52  cnf(c_0_32, plain, (X1!=k3_tarski(k3_tarski(k1_xboole_0))|X2!=k3_tarski(X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_29, c_0_21])).
% 0.19/0.52  cnf(c_0_33, plain, (X1!=k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_30, c_0_21])).
% 0.19/0.52  cnf(c_0_34, plain, (X1=k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)))|r2_hidden(esk9_2(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)),X1),X1)), inference(spm,[status(thm)],[c_0_26, c_0_31])).
% 0.19/0.52  cnf(c_0_35, plain, (X1!=k3_tarski(k3_tarski(k3_tarski(k1_xboole_0)))|~r2_hidden(X2,X1)), inference(er,[status(thm)],[c_0_32])).
% 0.19/0.52  cnf(c_0_36, plain, (~r2_hidden(X1,k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)))))), inference(er,[status(thm)],[c_0_33])).
% 0.19/0.52  cnf(c_0_37, plain, (k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_17, c_0_34])).
% 0.19/0.52  cnf(c_0_38, plain, (X1!=k3_tarski(k3_tarski(k3_tarski(k1_xboole_0)))|X2!=k2_zfmisc_1(X1,X3)|~r2_hidden(X4,X2)), inference(spm,[status(thm)],[c_0_35, c_0_18])).
% 0.19/0.52  cnf(c_0_39, plain, (~r2_hidden(X1,k3_tarski(k1_xboole_0))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.52  cnf(c_0_40, plain, (X1=k1_xboole_0|r2_hidden(esk9_2(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)),X1),X1)), inference(rw,[status(thm)],[c_0_34, c_0_37])).
% 0.19/0.52  cnf(c_0_41, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.52  fof(c_0_42, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.19/0.52  cnf(c_0_43, plain, (X1!=k3_tarski(k3_tarski(k3_tarski(k1_xboole_0)))|~r2_hidden(X2,k2_zfmisc_1(X1,X3))), inference(er,[status(thm)],[c_0_38])).
% 0.19/0.52  cnf(c_0_44, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.52  cnf(c_0_45, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_40])).
% 0.19/0.52  cnf(c_0_46, plain, (X1!=k3_tarski(k3_tarski(k1_xboole_0))|X2!=k2_zfmisc_1(X3,X1)|~r2_hidden(X4,X2)), inference(spm,[status(thm)],[c_0_29, c_0_41])).
% 0.19/0.52  fof(c_0_47, negated_conjecture, (((esk11_0!=k1_xboole_0|k2_zfmisc_1(esk11_0,esk12_0)!=k1_xboole_0)&(esk12_0!=k1_xboole_0|k2_zfmisc_1(esk11_0,esk12_0)!=k1_xboole_0))&(k2_zfmisc_1(esk11_0,esk12_0)=k1_xboole_0|(esk11_0=k1_xboole_0|esk12_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])])).
% 0.19/0.52  cnf(c_0_48, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k2_zfmisc_1(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_44]), c_0_44])).
% 0.19/0.52  cnf(c_0_49, plain, (X1=k1_xboole_0|r2_hidden(esk9_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_45]), c_0_44])).
% 0.19/0.52  cnf(c_0_50, plain, (X1!=k3_tarski(k3_tarski(k1_xboole_0))|~r2_hidden(X2,k2_zfmisc_1(X3,X1))), inference(er,[status(thm)],[c_0_46])).
% 0.19/0.52  cnf(c_0_51, negated_conjecture, (esk11_0!=k1_xboole_0|k2_zfmisc_1(esk11_0,esk12_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.52  cnf(c_0_52, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.52  cnf(c_0_53, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k2_zfmisc_1(X3,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_44]), c_0_44])).
% 0.19/0.52  cnf(c_0_54, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.52  cnf(c_0_55, negated_conjecture, (k2_zfmisc_1(esk11_0,esk12_0)=k1_xboole_0|esk11_0=k1_xboole_0|esk12_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.52  cnf(c_0_56, negated_conjecture, (esk11_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.52  cnf(c_0_57, negated_conjecture, (esk12_0!=k1_xboole_0|k2_zfmisc_1(esk11_0,esk12_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.52  cnf(c_0_58, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_49])).
% 0.19/0.52  cnf(c_0_59, plain, (r2_hidden(X1,k2_zfmisc_1(X2,X3))|X1!=k4_tarski(X4,X5)|~r2_hidden(X5,X3)|~r2_hidden(X4,X2)), inference(er,[status(thm)],[c_0_54])).
% 0.19/0.52  cnf(c_0_60, negated_conjecture, (k2_zfmisc_1(esk11_0,esk12_0)=k1_xboole_0|esk12_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.52  cnf(c_0_61, negated_conjecture, (esk12_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.52  cnf(c_0_62, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_59])).
% 0.19/0.52  cnf(c_0_63, negated_conjecture, (k2_zfmisc_1(esk11_0,esk12_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.52  cnf(c_0_64, negated_conjecture, (~r2_hidden(X1,esk12_0)|~r2_hidden(X2,esk11_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_17])).
% 0.19/0.52  cnf(c_0_65, negated_conjecture, (~r2_hidden(X1,esk11_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_49]), c_0_61])).
% 0.19/0.52  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_49]), c_0_56]), ['proof']).
% 0.19/0.52  # SZS output end CNFRefutation
% 0.19/0.52  # Proof object total steps             : 67
% 0.19/0.52  # Proof object clause steps            : 52
% 0.19/0.52  # Proof object formula steps           : 15
% 0.19/0.52  # Proof object conjectures             : 13
% 0.19/0.52  # Proof object clause conjectures      : 10
% 0.19/0.52  # Proof object formula conjectures     : 3
% 0.19/0.52  # Proof object initial clauses used    : 12
% 0.19/0.52  # Proof object initial formulas used   : 7
% 0.19/0.52  # Proof object generating inferences   : 33
% 0.19/0.52  # Proof object simplifying inferences  : 15
% 0.19/0.52  # Training examples: 0 positive, 0 negative
% 0.19/0.52  # Parsed axioms                        : 7
% 0.19/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.52  # Initial clauses                      : 25
% 0.19/0.52  # Removed in clause preprocessing      : 0
% 0.19/0.52  # Initial clauses in saturation        : 25
% 0.19/0.52  # Processed clauses                    : 2123
% 0.19/0.52  # ...of these trivial                  : 9
% 0.19/0.52  # ...subsumed                          : 1583
% 0.19/0.52  # ...remaining for further processing  : 531
% 0.19/0.52  # Other redundant clauses eliminated   : 1
% 0.19/0.52  # Clauses deleted for lack of memory   : 0
% 0.19/0.52  # Backward-subsumed                    : 13
% 0.19/0.52  # Backward-rewritten                   : 162
% 0.19/0.52  # Generated clauses                    : 9641
% 0.19/0.52  # ...of the previous two non-trivial   : 8569
% 0.19/0.52  # Contextual simplify-reflections      : 5
% 0.19/0.52  # Paramodulations                      : 9508
% 0.19/0.52  # Factorizations                       : 0
% 0.19/0.52  # Equation resolutions                 : 131
% 0.19/0.52  # Propositional unsat checks           : 0
% 0.19/0.52  #    Propositional check models        : 0
% 0.19/0.52  #    Propositional check unsatisfiable : 0
% 0.19/0.52  #    Propositional clauses             : 0
% 0.19/0.52  #    Propositional clauses after purity: 0
% 0.19/0.52  #    Propositional unsat core size     : 0
% 0.19/0.52  #    Propositional preprocessing time  : 0.000
% 0.19/0.52  #    Propositional encoding time       : 0.000
% 0.19/0.52  #    Propositional solver time         : 0.000
% 0.19/0.52  #    Success case prop preproc time    : 0.000
% 0.19/0.52  #    Success case prop encoding time   : 0.000
% 0.19/0.52  #    Success case prop solver time     : 0.000
% 0.19/0.52  # Current number of processed clauses  : 329
% 0.19/0.52  #    Positive orientable unit clauses  : 8
% 0.19/0.52  #    Positive unorientable unit clauses: 0
% 0.19/0.52  #    Negative unit clauses             : 4
% 0.19/0.52  #    Non-unit-clauses                  : 317
% 0.19/0.52  # Current number of unprocessed clauses: 5975
% 0.19/0.52  # ...number of literals in the above   : 32226
% 0.19/0.52  # Current number of archived formulas  : 0
% 0.19/0.52  # Current number of archived clauses   : 202
% 0.19/0.52  # Clause-clause subsumption calls (NU) : 9969
% 0.19/0.52  # Rec. Clause-clause subsumption calls : 5386
% 0.19/0.52  # Non-unit clause-clause subsumptions  : 970
% 0.19/0.52  # Unit Clause-clause subsumption calls : 266
% 0.19/0.52  # Rewrite failures with RHS unbound    : 0
% 0.19/0.52  # BW rewrite match attempts            : 29
% 0.19/0.52  # BW rewrite match successes           : 14
% 0.19/0.52  # Condensation attempts                : 0
% 0.19/0.52  # Condensation successes               : 0
% 0.19/0.52  # Termbank termtop insertions          : 96959
% 0.19/0.52  
% 0.19/0.52  # -------------------------------------------------
% 0.19/0.52  # User time                : 0.170 s
% 0.19/0.52  # System time              : 0.012 s
% 0.19/0.52  # Total time               : 0.182 s
% 0.19/0.52  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
