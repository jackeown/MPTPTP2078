%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:37 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 401 expanded)
%              Number of clauses        :   48 ( 197 expanded)
%              Number of leaves         :    7 (  92 expanded)
%              Depth                    :   11
%              Number of atoms          :  180 (1363 expanded)
%              Number of equality atoms :   48 ( 437 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

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

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(c_0_7,plain,(
    ! [X26,X27] :
      ( ( k2_zfmisc_1(X26,X27) != k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0 )
      & ( X26 != k1_xboole_0
        | k2_zfmisc_1(X26,X27) = k1_xboole_0 )
      & ( X27 != k1_xboole_0
        | k2_zfmisc_1(X26,X27) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

fof(c_0_9,plain,(
    ! [X28,X29] : ~ r2_hidden(X28,k2_zfmisc_1(X28,X29)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_10,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r2_hidden(esk1_2(X5,X6),X5)
        | r1_xboole_0(X5,X6) )
      & ( r2_hidden(esk1_2(X5,X6),X6)
        | r1_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & ( k10_relat_1(esk7_0,esk6_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk7_0),esk6_0) )
    & ( k10_relat_1(esk7_0,esk6_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk7_0),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_13,plain,(
    ! [X43,X44,X45,X47] :
      ( ( r2_hidden(esk5_3(X43,X44,X45),k2_relat_1(X45))
        | ~ r2_hidden(X43,k10_relat_1(X45,X44))
        | ~ v1_relat_1(X45) )
      & ( r2_hidden(k4_tarski(X43,esk5_3(X43,X44,X45)),X45)
        | ~ r2_hidden(X43,k10_relat_1(X45,X44))
        | ~ v1_relat_1(X45) )
      & ( r2_hidden(esk5_3(X43,X44,X45),X44)
        | ~ r2_hidden(X43,k10_relat_1(X45,X44))
        | ~ v1_relat_1(X45) )
      & ( ~ r2_hidden(X47,k2_relat_1(X45))
        | ~ r2_hidden(k4_tarski(X43,X47),X45)
        | ~ r2_hidden(X47,X44)
        | r2_hidden(X43,k10_relat_1(X45,X44))
        | ~ v1_relat_1(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X32,X33,X34,X36,X37,X38,X39,X41] :
      ( ( ~ r2_hidden(X34,X33)
        | r2_hidden(k4_tarski(esk2_3(X32,X33,X34),X34),X32)
        | X33 != k2_relat_1(X32) )
      & ( ~ r2_hidden(k4_tarski(X37,X36),X32)
        | r2_hidden(X36,X33)
        | X33 != k2_relat_1(X32) )
      & ( ~ r2_hidden(esk3_2(X38,X39),X39)
        | ~ r2_hidden(k4_tarski(X41,esk3_2(X38,X39)),X38)
        | X39 = k2_relat_1(X38) )
      & ( r2_hidden(esk3_2(X38,X39),X39)
        | r2_hidden(k4_tarski(esk4_2(X38,X39),esk3_2(X38,X39)),X38)
        | X39 = k2_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k10_relat_1(esk7_0,esk6_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( k10_relat_1(esk7_0,esk6_0) = k1_xboole_0
    | ~ r2_hidden(X1,k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk5_3(X1,X2,esk7_0),k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,k10_relat_1(esk7_0,X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( X1 = k2_relat_1(k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X15,X16] :
      ( ( ~ r1_xboole_0(X15,X16)
        | k4_xboole_0(X15,X16) = X15 )
      & ( k4_xboole_0(X15,X16) != X15
        | r1_xboole_0(X15,X16) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_31,negated_conjecture,
    ( k10_relat_1(esk7_0,esk6_0) = k1_xboole_0
    | ~ r2_hidden(esk5_3(X1,X2,esk7_0),esk6_0)
    | ~ r2_hidden(X1,k10_relat_1(esk7_0,X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk5_3(X1,X2,esk7_0),X2)
    | ~ r2_hidden(X1,k10_relat_1(esk7_0,X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_20])).

cnf(c_0_33,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( k10_relat_1(esk7_0,esk6_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(esk2_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( k10_relat_1(esk7_0,esk6_0) = k1_xboole_0
    | ~ r2_hidden(X1,k10_relat_1(esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_27,c_0_33])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk7_0),esk6_0),k2_relat_1(esk7_0))
    | k10_relat_1(esk7_0,esk6_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk7_0,X2))
    | ~ r2_hidden(k4_tarski(X1,X3),esk7_0)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_20])).

cnf(c_0_46,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_38])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk7_0),esk6_0),esk6_0)
    | k10_relat_1(esk7_0,esk6_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( k10_relat_1(esk7_0,esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(k2_relat_1(esk7_0),esk6_0) != k2_relat_1(esk7_0)
    | k10_relat_1(esk7_0,esk6_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_2(X1,k2_relat_1(esk7_0)),X1)
    | k10_relat_1(esk7_0,esk6_0) != k1_xboole_0
    | ~ r2_hidden(esk1_2(k2_relat_1(esk7_0),esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k2_relat_1(esk7_0),X1),k10_relat_1(esk7_0,X2))
    | ~ r2_hidden(X1,k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_2(X3,X1),X1)
    | ~ r2_hidden(esk1_2(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk7_0),esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(k2_relat_1(esk7_0),esk6_0) != k2_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_50])])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk1_2(X1,k2_relat_1(esk7_0)),X1)
    | ~ r2_hidden(esk1_2(k2_relat_1(esk7_0),esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_50])])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_50]),c_0_21])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k2_relat_1(esk7_0)),k2_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k2_relat_1(esk7_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:50:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.56  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S032I
% 0.20/0.56  # and selection function SelectUnlessUniqMax.
% 0.20/0.56  #
% 0.20/0.56  # Preprocessing time       : 0.029 s
% 0.20/0.56  # Presaturation interreduction done
% 0.20/0.56  
% 0.20/0.56  # Proof found!
% 0.20/0.56  # SZS status Theorem
% 0.20/0.56  # SZS output start CNFRefutation
% 0.20/0.56  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.56  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 0.20/0.56  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.20/0.56  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.56  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 0.20/0.56  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.20/0.56  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.56  fof(c_0_7, plain, ![X26, X27]:((k2_zfmisc_1(X26,X27)!=k1_xboole_0|(X26=k1_xboole_0|X27=k1_xboole_0))&((X26!=k1_xboole_0|k2_zfmisc_1(X26,X27)=k1_xboole_0)&(X27!=k1_xboole_0|k2_zfmisc_1(X26,X27)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.56  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.20/0.56  fof(c_0_9, plain, ![X28, X29]:~r2_hidden(X28,k2_zfmisc_1(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.20/0.56  cnf(c_0_10, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.56  fof(c_0_11, plain, ![X5, X6, X8, X9, X10]:(((r2_hidden(esk1_2(X5,X6),X5)|r1_xboole_0(X5,X6))&(r2_hidden(esk1_2(X5,X6),X6)|r1_xboole_0(X5,X6)))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|~r1_xboole_0(X8,X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.56  fof(c_0_12, negated_conjecture, (v1_relat_1(esk7_0)&((k10_relat_1(esk7_0,esk6_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk7_0),esk6_0))&(k10_relat_1(esk7_0,esk6_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk7_0),esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.20/0.56  fof(c_0_13, plain, ![X43, X44, X45, X47]:((((r2_hidden(esk5_3(X43,X44,X45),k2_relat_1(X45))|~r2_hidden(X43,k10_relat_1(X45,X44))|~v1_relat_1(X45))&(r2_hidden(k4_tarski(X43,esk5_3(X43,X44,X45)),X45)|~r2_hidden(X43,k10_relat_1(X45,X44))|~v1_relat_1(X45)))&(r2_hidden(esk5_3(X43,X44,X45),X44)|~r2_hidden(X43,k10_relat_1(X45,X44))|~v1_relat_1(X45)))&(~r2_hidden(X47,k2_relat_1(X45))|~r2_hidden(k4_tarski(X43,X47),X45)|~r2_hidden(X47,X44)|r2_hidden(X43,k10_relat_1(X45,X44))|~v1_relat_1(X45))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.20/0.56  cnf(c_0_14, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.56  cnf(c_0_15, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_10])).
% 0.20/0.56  fof(c_0_16, plain, ![X32, X33, X34, X36, X37, X38, X39, X41]:(((~r2_hidden(X34,X33)|r2_hidden(k4_tarski(esk2_3(X32,X33,X34),X34),X32)|X33!=k2_relat_1(X32))&(~r2_hidden(k4_tarski(X37,X36),X32)|r2_hidden(X36,X33)|X33!=k2_relat_1(X32)))&((~r2_hidden(esk3_2(X38,X39),X39)|~r2_hidden(k4_tarski(X41,esk3_2(X38,X39)),X38)|X39=k2_relat_1(X38))&(r2_hidden(esk3_2(X38,X39),X39)|r2_hidden(k4_tarski(esk4_2(X38,X39),esk3_2(X38,X39)),X38)|X39=k2_relat_1(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.20/0.56  cnf(c_0_17, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.56  cnf(c_0_18, negated_conjecture, (k10_relat_1(esk7_0,esk6_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.56  cnf(c_0_19, plain, (r2_hidden(esk5_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.56  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.56  cnf(c_0_21, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.56  cnf(c_0_22, plain, (r2_hidden(esk3_2(X1,X2),X2)|r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.56  cnf(c_0_23, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.56  cnf(c_0_24, negated_conjecture, (k10_relat_1(esk7_0,esk6_0)=k1_xboole_0|~r2_hidden(X1,k2_relat_1(esk7_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.56  cnf(c_0_25, negated_conjecture, (r2_hidden(esk5_3(X1,X2,esk7_0),k2_relat_1(esk7_0))|~r2_hidden(X1,k10_relat_1(esk7_0,X2))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.56  cnf(c_0_26, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.56  cnf(c_0_27, plain, (X1=k2_relat_1(k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.56  cnf(c_0_28, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.56  cnf(c_0_29, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_23])).
% 0.20/0.56  fof(c_0_30, plain, ![X15, X16]:((~r1_xboole_0(X15,X16)|k4_xboole_0(X15,X16)=X15)&(k4_xboole_0(X15,X16)!=X15|r1_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.56  cnf(c_0_31, negated_conjecture, (k10_relat_1(esk7_0,esk6_0)=k1_xboole_0|~r2_hidden(esk5_3(X1,X2,esk7_0),esk6_0)|~r2_hidden(X1,k10_relat_1(esk7_0,X2))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.56  cnf(c_0_32, negated_conjecture, (r2_hidden(esk5_3(X1,X2,esk7_0),X2)|~r2_hidden(X1,k10_relat_1(esk7_0,X2))), inference(spm,[status(thm)],[c_0_26, c_0_20])).
% 0.20/0.56  cnf(c_0_33, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_27])).
% 0.20/0.56  cnf(c_0_34, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.56  cnf(c_0_35, negated_conjecture, (k10_relat_1(esk7_0,esk6_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.56  cnf(c_0_36, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.56  cnf(c_0_37, plain, (r2_hidden(k4_tarski(esk2_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.56  cnf(c_0_38, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.56  cnf(c_0_39, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.56  cnf(c_0_40, negated_conjecture, (k10_relat_1(esk7_0,esk6_0)=k1_xboole_0|~r2_hidden(X1,k10_relat_1(esk7_0,esk6_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.56  cnf(c_0_41, plain, (X1=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[c_0_27, c_0_33])).
% 0.20/0.56  cnf(c_0_42, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.56  cnf(c_0_43, plain, (r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_17, c_0_34])).
% 0.20/0.56  cnf(c_0_44, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk7_0),esk6_0),k2_relat_1(esk7_0))|k10_relat_1(esk7_0,esk6_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 0.20/0.56  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,k10_relat_1(esk7_0,X2))|~r2_hidden(k4_tarski(X1,X3),esk7_0)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_36, c_0_20])).
% 0.20/0.56  cnf(c_0_46, plain, (r2_hidden(k4_tarski(esk2_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_37])).
% 0.20/0.56  cnf(c_0_47, plain, (r2_hidden(esk1_2(X1,X2),X2)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_17, c_0_38])).
% 0.20/0.56  cnf(c_0_48, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_39, c_0_34])).
% 0.20/0.56  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk7_0),esk6_0),esk6_0)|k10_relat_1(esk7_0,esk6_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_38])).
% 0.20/0.56  cnf(c_0_50, negated_conjecture, (k10_relat_1(esk7_0,esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.56  cnf(c_0_51, negated_conjecture, (k4_xboole_0(k2_relat_1(esk7_0),esk6_0)!=k2_relat_1(esk7_0)|k10_relat_1(esk7_0,esk6_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_42])).
% 0.20/0.56  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_2(X1,k2_relat_1(esk7_0)),X1)|k10_relat_1(esk7_0,esk6_0)!=k1_xboole_0|~r2_hidden(esk1_2(k2_relat_1(esk7_0),esk6_0),X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.56  cnf(c_0_53, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k2_relat_1(esk7_0),X1),k10_relat_1(esk7_0,X2))|~r2_hidden(X1,k2_relat_1(esk7_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.56  cnf(c_0_54, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_2(X3,X1),X1)|~r2_hidden(esk1_2(X1,X2),X3)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.56  cnf(c_0_55, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk7_0),esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50])])).
% 0.20/0.56  cnf(c_0_56, negated_conjecture, (k4_xboole_0(k2_relat_1(esk7_0),esk6_0)!=k2_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_50])])).
% 0.20/0.56  cnf(c_0_57, negated_conjecture, (r2_hidden(esk1_2(X1,k2_relat_1(esk7_0)),X1)|~r2_hidden(esk1_2(k2_relat_1(esk7_0),esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_50])])).
% 0.20/0.56  cnf(c_0_58, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 0.20/0.56  cnf(c_0_59, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk7_0))|~r2_hidden(X1,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_50]), c_0_21])).
% 0.20/0.56  cnf(c_0_60, negated_conjecture, (r2_hidden(esk1_2(esk6_0,k2_relat_1(esk7_0)),k2_relat_1(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.20/0.56  cnf(c_0_61, negated_conjecture, (r2_hidden(esk1_2(esk6_0,k2_relat_1(esk7_0)),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_56])).
% 0.20/0.56  cnf(c_0_62, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])]), ['proof']).
% 0.20/0.56  # SZS output end CNFRefutation
% 0.20/0.56  # Proof object total steps             : 63
% 0.20/0.56  # Proof object clause steps            : 48
% 0.20/0.56  # Proof object formula steps           : 15
% 0.20/0.56  # Proof object conjectures             : 25
% 0.20/0.56  # Proof object clause conjectures      : 22
% 0.20/0.56  # Proof object formula conjectures     : 3
% 0.20/0.56  # Proof object initial clauses used    : 16
% 0.20/0.56  # Proof object initial formulas used   : 7
% 0.20/0.56  # Proof object generating inferences   : 24
% 0.20/0.56  # Proof object simplifying inferences  : 16
% 0.20/0.56  # Training examples: 0 positive, 0 negative
% 0.20/0.56  # Parsed axioms                        : 15
% 0.20/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.56  # Initial clauses                      : 28
% 0.20/0.56  # Removed in clause preprocessing      : 4
% 0.20/0.56  # Initial clauses in saturation        : 24
% 0.20/0.56  # Processed clauses                    : 1339
% 0.20/0.56  # ...of these trivial                  : 30
% 0.20/0.56  # ...subsumed                          : 843
% 0.20/0.56  # ...remaining for further processing  : 466
% 0.20/0.56  # Other redundant clauses eliminated   : 5
% 0.20/0.56  # Clauses deleted for lack of memory   : 0
% 0.20/0.56  # Backward-subsumed                    : 1
% 0.20/0.56  # Backward-rewritten                   : 31
% 0.20/0.56  # Generated clauses                    : 20696
% 0.20/0.56  # ...of the previous two non-trivial   : 15774
% 0.20/0.56  # Contextual simplify-reflections      : 1
% 0.20/0.56  # Paramodulations                      : 20688
% 0.20/0.56  # Factorizations                       : 3
% 0.20/0.56  # Equation resolutions                 : 5
% 0.20/0.56  # Propositional unsat checks           : 0
% 0.20/0.56  #    Propositional check models        : 0
% 0.20/0.56  #    Propositional check unsatisfiable : 0
% 0.20/0.56  #    Propositional clauses             : 0
% 0.20/0.56  #    Propositional clauses after purity: 0
% 0.20/0.56  #    Propositional unsat core size     : 0
% 0.20/0.56  #    Propositional preprocessing time  : 0.000
% 0.20/0.56  #    Propositional encoding time       : 0.000
% 0.20/0.56  #    Propositional solver time         : 0.000
% 0.20/0.56  #    Success case prop preproc time    : 0.000
% 0.20/0.56  #    Success case prop encoding time   : 0.000
% 0.20/0.56  #    Success case prop solver time     : 0.000
% 0.20/0.56  # Current number of processed clauses  : 406
% 0.20/0.56  #    Positive orientable unit clauses  : 18
% 0.20/0.56  #    Positive unorientable unit clauses: 0
% 0.20/0.56  #    Negative unit clauses             : 4
% 0.20/0.56  #    Non-unit-clauses                  : 384
% 0.20/0.56  # Current number of unprocessed clauses: 14352
% 0.20/0.56  # ...number of literals in the above   : 34285
% 0.20/0.56  # Current number of archived formulas  : 0
% 0.20/0.56  # Current number of archived clauses   : 60
% 0.20/0.56  # Clause-clause subsumption calls (NU) : 36114
% 0.20/0.56  # Rec. Clause-clause subsumption calls : 35124
% 0.20/0.56  # Non-unit clause-clause subsumptions  : 685
% 0.20/0.56  # Unit Clause-clause subsumption calls : 44
% 0.20/0.56  # Rewrite failures with RHS unbound    : 0
% 0.20/0.56  # BW rewrite match attempts            : 9
% 0.20/0.56  # BW rewrite match successes           : 5
% 0.20/0.56  # Condensation attempts                : 0
% 0.20/0.56  # Condensation successes               : 0
% 0.20/0.56  # Termbank termtop insertions          : 333586
% 0.20/0.56  
% 0.20/0.56  # -------------------------------------------------
% 0.20/0.56  # User time                : 0.209 s
% 0.20/0.56  # System time              : 0.013 s
% 0.20/0.56  # Total time               : 0.223 s
% 0.20/0.56  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
