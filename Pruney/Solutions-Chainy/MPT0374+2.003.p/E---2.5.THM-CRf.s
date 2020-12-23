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
% DateTime   : Thu Dec  3 10:46:51 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 465 expanded)
%              Number of clauses        :   68 ( 217 expanded)
%              Number of leaves         :   13 ( 116 expanded)
%              Depth                    :   23
%              Number of atoms          :  259 (1663 expanded)
%              Number of equality atoms :   72 ( 428 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(dt_k1_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t56_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ! [X3] :
          ( m1_subset_1(X3,X1)
         => ( X1 != k1_xboole_0
           => m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t55_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ( X1 != k1_xboole_0
       => m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t73_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(c_0_13,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_14,plain,(
    ! [X45] : m1_subset_1(k1_subset_1(X45),k1_zfmisc_1(X45)) ),
    inference(variable_rename,[status(thm)],[dt_k1_subset_1])).

fof(c_0_15,plain,(
    ! [X43] : k1_subset_1(X43) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X19] : k4_xboole_0(k1_xboole_0,X19) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_18,plain,(
    ! [X46,X47,X48] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(X46))
      | ~ r2_hidden(X48,X47)
      | r2_hidden(X48,X46) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_19,plain,
    ( m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,X1)
       => ! [X3] :
            ( m1_subset_1(X3,X1)
           => ( X1 != k1_xboole_0
             => m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t56_subset_1])).

fof(c_0_27,plain,(
    ! [X41,X42] :
      ( ( ~ m1_subset_1(X42,X41)
        | r2_hidden(X42,X41)
        | v1_xboole_0(X41) )
      & ( ~ r2_hidden(X42,X41)
        | m1_subset_1(X42,X41)
        | v1_xboole_0(X41) )
      & ( ~ m1_subset_1(X42,X41)
        | v1_xboole_0(X42)
        | ~ v1_xboole_0(X41) )
      & ( ~ v1_xboole_0(X42)
        | m1_subset_1(X42,X41)
        | ~ v1_xboole_0(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_30,plain,(
    ! [X14] :
      ( ~ v1_xboole_0(X14)
      | X14 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_31,plain,(
    ! [X27,X28,X29,X30,X31,X32] :
      ( ( ~ r2_hidden(X29,X28)
        | r1_tarski(X29,X27)
        | X28 != k1_zfmisc_1(X27) )
      & ( ~ r1_tarski(X30,X27)
        | r2_hidden(X30,X28)
        | X28 != k1_zfmisc_1(X27) )
      & ( ~ r2_hidden(esk3_2(X31,X32),X32)
        | ~ r1_tarski(esk3_2(X31,X32),X31)
        | X32 = k1_zfmisc_1(X31) )
      & ( r2_hidden(esk3_2(X31,X32),X32)
        | r1_tarski(esk3_2(X31,X32),X31)
        | X32 = k1_zfmisc_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_32,plain,(
    ! [X53,X54] :
      ( ~ m1_subset_1(X54,X53)
      | X53 = k1_xboole_0
      | m1_subset_1(k1_tarski(X54),k1_zfmisc_1(X53)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_subset_1])])).

fof(c_0_33,negated_conjecture,
    ( m1_subset_1(esk5_0,esk4_0)
    & m1_subset_1(esk6_0,esk4_0)
    & esk4_0 != k1_xboole_0
    & ~ m1_subset_1(k2_tarski(esk5_0,esk6_0),k1_zfmisc_1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_22])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,plain,(
    ! [X15,X16] :
      ( ( k4_xboole_0(X15,X16) != k1_xboole_0
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | k4_xboole_0(X15,X16) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( X2 = k1_xboole_0
    | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | m1_subset_1(esk1_3(k1_xboole_0,X2,X1),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk6_0),k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | m1_subset_1(k1_tarski(esk1_3(k1_xboole_0,X2,X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_42])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk4_0))
    | r2_hidden(k1_tarski(esk6_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_51,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X20
        | X21 != k1_tarski(X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k1_tarski(X20) )
      & ( ~ r2_hidden(esk2_2(X24,X25),X25)
        | esk2_2(X24,X25) != X24
        | X25 = k1_tarski(X24) )
      & ( r2_hidden(esk2_2(X24,X25),X25)
        | esk2_2(X24,X25) = X24
        | X25 = k1_tarski(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | v1_xboole_0(k1_tarski(esk1_3(k1_xboole_0,X2,X1)))
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk6_0),esk4_0) = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk6_0),esk4_0) = k1_xboole_0
    | v1_xboole_0(k1_tarski(esk1_3(k1_xboole_0,X1,esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,k1_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_46])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).

cnf(c_0_58,negated_conjecture,
    ( k1_tarski(esk1_3(k1_xboole_0,X1,esk4_0)) = k1_xboole_0
    | k4_xboole_0(k1_tarski(esk6_0),esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_55])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_60,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_61,negated_conjecture,
    ( X1 = k4_xboole_0(k1_tarski(esk6_0),X2)
    | r2_hidden(esk1_3(k1_tarski(esk6_0),X2,X1),esk4_0)
    | r2_hidden(esk1_3(k1_tarski(esk6_0),X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_29])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk6_0),esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_28])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_65,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(k1_tarski(esk6_0),esk4_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk1_3(k1_tarski(esk6_0),esk4_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_65]),c_0_62])]),c_0_41])).

cnf(c_0_69,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | v1_xboole_0(k1_zfmisc_1(X2))
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_66])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_67]),c_0_28])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk1_3(k1_tarski(esk6_0),esk4_0,esk4_0),esk4_0)
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_68])).

cnf(c_0_72,plain,
    ( m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_73,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk1_3(k1_tarski(esk6_0),esk4_0,esk4_0)),k1_zfmisc_1(esk4_0))
    | v1_xboole_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_71]),c_0_41])).

cnf(c_0_75,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( v1_xboole_0(k1_tarski(esk1_3(k1_tarski(esk6_0),esk4_0,esk4_0)))
    | v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_74])).

cnf(c_0_77,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(ef,[status(thm)],[c_0_75])).

fof(c_0_78,plain,(
    ! [X38,X39,X40] :
      ( ( r2_hidden(X38,X40)
        | k4_xboole_0(k2_tarski(X38,X39),X40) != k1_xboole_0 )
      & ( r2_hidden(X39,X40)
        | k4_xboole_0(k2_tarski(X38,X39),X40) != k1_xboole_0 )
      & ( ~ r2_hidden(X38,X40)
        | ~ r2_hidden(X39,X40)
        | k4_xboole_0(k2_tarski(X38,X39),X40) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_zfmisc_1])])])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk4_0))
    | v1_xboole_0(k1_tarski(esk1_3(k1_tarski(esk6_0),esk4_0,esk4_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_73]),c_0_77])).

cnf(c_0_80,plain,
    ( k4_xboole_0(k2_tarski(X1,X3),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | r2_hidden(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_40])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_83,negated_conjecture,
    ( k1_tarski(esk1_3(k1_tarski(esk6_0),esk4_0,esk4_0)) = k1_xboole_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_79])).

cnf(c_0_84,plain,
    ( m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X3))
    | v1_xboole_0(k1_zfmisc_1(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_69,c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_81]),c_0_41])).

cnf(c_0_86,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_83]),c_0_28])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(k2_tarski(X1,esk6_0),k1_zfmisc_1(esk4_0))
    | v1_xboole_0(k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_86]),c_0_41])).

cnf(c_0_90,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(esk5_0,esk6_0),k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_91,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92])])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_93]),c_0_41]),
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
% 0.14/0.34  % DateTime   : Tue Dec  1 10:51:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.69/0.85  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.69/0.85  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.69/0.85  #
% 0.69/0.85  # Preprocessing time       : 0.028 s
% 0.69/0.85  # Presaturation interreduction done
% 0.69/0.85  
% 0.69/0.85  # Proof found!
% 0.69/0.85  # SZS status Theorem
% 0.69/0.85  # SZS output start CNFRefutation
% 0.69/0.85  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.69/0.85  fof(dt_k1_subset_1, axiom, ![X1]:m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 0.69/0.85  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.69/0.85  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.69/0.85  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.69/0.85  fof(t56_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_subset_1)).
% 0.69/0.85  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.69/0.85  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.69/0.85  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.69/0.85  fof(t55_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 0.69/0.85  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.69/0.85  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.69/0.85  fof(t73_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 0.69/0.85  fof(c_0_13, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.69/0.85  fof(c_0_14, plain, ![X45]:m1_subset_1(k1_subset_1(X45),k1_zfmisc_1(X45)), inference(variable_rename,[status(thm)],[dt_k1_subset_1])).
% 0.69/0.85  fof(c_0_15, plain, ![X43]:k1_subset_1(X43)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.69/0.85  cnf(c_0_16, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.69/0.85  fof(c_0_17, plain, ![X19]:k4_xboole_0(k1_xboole_0,X19)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.69/0.85  fof(c_0_18, plain, ![X46, X47, X48]:(~m1_subset_1(X47,k1_zfmisc_1(X46))|(~r2_hidden(X48,X47)|r2_hidden(X48,X46))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.69/0.85  cnf(c_0_19, plain, (m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.69/0.85  cnf(c_0_20, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.69/0.85  cnf(c_0_21, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_16])).
% 0.69/0.85  cnf(c_0_22, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.69/0.85  cnf(c_0_23, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.69/0.85  cnf(c_0_24, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.69/0.85  cnf(c_0_25, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.69/0.85  fof(c_0_26, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X1)))))), inference(assume_negation,[status(cth)],[t56_subset_1])).
% 0.69/0.85  fof(c_0_27, plain, ![X41, X42]:(((~m1_subset_1(X42,X41)|r2_hidden(X42,X41)|v1_xboole_0(X41))&(~r2_hidden(X42,X41)|m1_subset_1(X42,X41)|v1_xboole_0(X41)))&((~m1_subset_1(X42,X41)|v1_xboole_0(X42)|~v1_xboole_0(X41))&(~v1_xboole_0(X42)|m1_subset_1(X42,X41)|~v1_xboole_0(X41)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.69/0.85  cnf(c_0_28, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.69/0.85  cnf(c_0_29, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.69/0.85  fof(c_0_30, plain, ![X14]:(~v1_xboole_0(X14)|X14=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.69/0.85  fof(c_0_31, plain, ![X27, X28, X29, X30, X31, X32]:(((~r2_hidden(X29,X28)|r1_tarski(X29,X27)|X28!=k1_zfmisc_1(X27))&(~r1_tarski(X30,X27)|r2_hidden(X30,X28)|X28!=k1_zfmisc_1(X27)))&((~r2_hidden(esk3_2(X31,X32),X32)|~r1_tarski(esk3_2(X31,X32),X31)|X32=k1_zfmisc_1(X31))&(r2_hidden(esk3_2(X31,X32),X32)|r1_tarski(esk3_2(X31,X32),X31)|X32=k1_zfmisc_1(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.69/0.85  fof(c_0_32, plain, ![X53, X54]:(~m1_subset_1(X54,X53)|(X53=k1_xboole_0|m1_subset_1(k1_tarski(X54),k1_zfmisc_1(X53)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_subset_1])])).
% 0.69/0.85  fof(c_0_33, negated_conjecture, (m1_subset_1(esk5_0,esk4_0)&(m1_subset_1(esk6_0,esk4_0)&(esk4_0!=k1_xboole_0&~m1_subset_1(k2_tarski(esk5_0,esk6_0),k1_zfmisc_1(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.69/0.85  cnf(c_0_34, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.69/0.85  cnf(c_0_35, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_22])).
% 0.69/0.85  cnf(c_0_36, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.69/0.85  fof(c_0_37, plain, ![X15, X16]:((k4_xboole_0(X15,X16)!=k1_xboole_0|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|k4_xboole_0(X15,X16)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.69/0.85  cnf(c_0_38, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.69/0.85  cnf(c_0_39, plain, (X2=k1_xboole_0|m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.69/0.85  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.69/0.85  cnf(c_0_41, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.69/0.85  cnf(c_0_42, plain, (X1=k1_xboole_0|m1_subset_1(esk1_3(k1_xboole_0,X2,X1),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.69/0.85  cnf(c_0_43, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.69/0.85  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_38])).
% 0.69/0.85  cnf(c_0_45, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.69/0.85  cnf(c_0_46, negated_conjecture, (m1_subset_1(k1_tarski(esk6_0),k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.69/0.85  cnf(c_0_47, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.69/0.85  cnf(c_0_48, plain, (X1=k1_xboole_0|m1_subset_1(k1_tarski(esk1_3(k1_xboole_0,X2,X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_39, c_0_42])).
% 0.69/0.85  cnf(c_0_49, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.69/0.85  cnf(c_0_50, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(esk4_0))|r2_hidden(k1_tarski(esk6_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.69/0.85  fof(c_0_51, plain, ![X20, X21, X22, X23, X24, X25]:(((~r2_hidden(X22,X21)|X22=X20|X21!=k1_tarski(X20))&(X23!=X20|r2_hidden(X23,X21)|X21!=k1_tarski(X20)))&((~r2_hidden(esk2_2(X24,X25),X25)|esk2_2(X24,X25)!=X24|X25=k1_tarski(X24))&(r2_hidden(esk2_2(X24,X25),X25)|esk2_2(X24,X25)=X24|X25=k1_tarski(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.69/0.85  cnf(c_0_52, plain, (X1=k1_xboole_0|v1_xboole_0(k1_tarski(esk1_3(k1_xboole_0,X2,X1)))|~v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.69/0.85  cnf(c_0_53, negated_conjecture, (k4_xboole_0(k1_tarski(esk6_0),esk4_0)=k1_xboole_0|v1_xboole_0(k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.69/0.85  cnf(c_0_54, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.69/0.85  cnf(c_0_55, negated_conjecture, (k4_xboole_0(k1_tarski(esk6_0),esk4_0)=k1_xboole_0|v1_xboole_0(k1_tarski(esk1_3(k1_xboole_0,X1,esk4_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_41])).
% 0.69/0.85  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,k1_tarski(esk6_0))), inference(spm,[status(thm)],[c_0_23, c_0_46])).
% 0.69/0.85  cnf(c_0_57, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).
% 0.69/0.85  cnf(c_0_58, negated_conjecture, (k1_tarski(esk1_3(k1_xboole_0,X1,esk4_0))=k1_xboole_0|k4_xboole_0(k1_tarski(esk6_0),esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_55])).
% 0.69/0.85  cnf(c_0_59, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.69/0.85  cnf(c_0_60, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.69/0.85  cnf(c_0_61, negated_conjecture, (X1=k4_xboole_0(k1_tarski(esk6_0),X2)|r2_hidden(esk1_3(k1_tarski(esk6_0),X2,X1),esk4_0)|r2_hidden(esk1_3(k1_tarski(esk6_0),X2,X1),X1)), inference(spm,[status(thm)],[c_0_56, c_0_29])).
% 0.69/0.85  cnf(c_0_62, negated_conjecture, (k4_xboole_0(k1_tarski(esk6_0),esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_28])).
% 0.69/0.85  cnf(c_0_63, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_59])).
% 0.69/0.85  cnf(c_0_64, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.69/0.85  cnf(c_0_65, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk1_3(k1_tarski(esk6_0),esk4_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.69/0.85  cnf(c_0_66, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.69/0.85  cnf(c_0_67, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.69/0.85  cnf(c_0_68, negated_conjecture, (r2_hidden(esk1_3(k1_tarski(esk6_0),esk4_0,esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_65]), c_0_62])]), c_0_41])).
% 0.69/0.85  cnf(c_0_69, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|v1_xboole_0(k1_zfmisc_1(X2))|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_66])).
% 0.69/0.85  cnf(c_0_70, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_67]), c_0_28])).
% 0.69/0.85  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk1_3(k1_tarski(esk6_0),esk4_0,esk4_0),esk4_0)|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_34, c_0_68])).
% 0.69/0.85  cnf(c_0_72, plain, (m1_subset_1(X1,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.69/0.85  cnf(c_0_73, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))|v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.69/0.85  cnf(c_0_74, negated_conjecture, (m1_subset_1(k1_tarski(esk1_3(k1_tarski(esk6_0),esk4_0,esk4_0)),k1_zfmisc_1(esk4_0))|v1_xboole_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_71]), c_0_41])).
% 0.69/0.85  cnf(c_0_75, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))|m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.69/0.85  cnf(c_0_76, negated_conjecture, (v1_xboole_0(k1_tarski(esk1_3(k1_tarski(esk6_0),esk4_0,esk4_0)))|v1_xboole_0(esk4_0)|~v1_xboole_0(k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_74])).
% 0.69/0.85  cnf(c_0_77, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))|~v1_xboole_0(X1)), inference(ef,[status(thm)],[c_0_75])).
% 0.69/0.85  fof(c_0_78, plain, ![X38, X39, X40]:(((r2_hidden(X38,X40)|k4_xboole_0(k2_tarski(X38,X39),X40)!=k1_xboole_0)&(r2_hidden(X39,X40)|k4_xboole_0(k2_tarski(X38,X39),X40)!=k1_xboole_0))&(~r2_hidden(X38,X40)|~r2_hidden(X39,X40)|k4_xboole_0(k2_tarski(X38,X39),X40)=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_zfmisc_1])])])).
% 0.69/0.85  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk4_0))|v1_xboole_0(k1_tarski(esk1_3(k1_tarski(esk6_0),esk4_0,esk4_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_73]), c_0_77])).
% 0.69/0.85  cnf(c_0_80, plain, (k4_xboole_0(k2_tarski(X1,X3),X2)=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.69/0.85  cnf(c_0_81, negated_conjecture, (v1_xboole_0(esk4_0)|r2_hidden(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_45, c_0_40])).
% 0.69/0.85  cnf(c_0_82, negated_conjecture, (m1_subset_1(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.69/0.85  cnf(c_0_83, negated_conjecture, (k1_tarski(esk1_3(k1_tarski(esk6_0),esk4_0,esk4_0))=k1_xboole_0|m1_subset_1(esk4_0,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_36, c_0_79])).
% 0.69/0.85  cnf(c_0_84, plain, (m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X3))|v1_xboole_0(k1_zfmisc_1(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_69, c_0_80])).
% 0.69/0.85  cnf(c_0_85, negated_conjecture, (r2_hidden(esk6_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_81]), c_0_41])).
% 0.69/0.85  cnf(c_0_86, negated_conjecture, (v1_xboole_0(esk4_0)|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_45, c_0_82])).
% 0.69/0.85  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_83]), c_0_28])).
% 0.69/0.85  cnf(c_0_88, negated_conjecture, (m1_subset_1(k2_tarski(X1,esk6_0),k1_zfmisc_1(esk4_0))|v1_xboole_0(k1_zfmisc_1(esk4_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.69/0.85  cnf(c_0_89, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_86]), c_0_41])).
% 0.69/0.85  cnf(c_0_90, negated_conjecture, (~m1_subset_1(k2_tarski(esk5_0,esk6_0),k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.69/0.85  cnf(c_0_91, negated_conjecture, (v1_xboole_0(esk4_0)|~v1_xboole_0(k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_87])).
% 0.69/0.85  cnf(c_0_92, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])).
% 0.69/0.85  cnf(c_0_93, negated_conjecture, (v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_92])])).
% 0.69/0.85  cnf(c_0_94, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_93]), c_0_41]), ['proof']).
% 0.69/0.85  # SZS output end CNFRefutation
% 0.69/0.85  # Proof object total steps             : 95
% 0.69/0.85  # Proof object clause steps            : 68
% 0.69/0.85  # Proof object formula steps           : 27
% 0.69/0.85  # Proof object conjectures             : 32
% 0.69/0.85  # Proof object clause conjectures      : 29
% 0.69/0.85  # Proof object formula conjectures     : 3
% 0.69/0.85  # Proof object initial clauses used    : 23
% 0.69/0.85  # Proof object initial formulas used   : 13
% 0.69/0.85  # Proof object generating inferences   : 39
% 0.69/0.85  # Proof object simplifying inferences  : 26
% 0.69/0.85  # Training examples: 0 positive, 0 negative
% 0.69/0.85  # Parsed axioms                        : 19
% 0.69/0.85  # Removed by relevancy pruning/SinE    : 0
% 0.69/0.85  # Initial clauses                      : 40
% 0.69/0.85  # Removed in clause preprocessing      : 2
% 0.69/0.85  # Initial clauses in saturation        : 38
% 0.69/0.85  # Processed clauses                    : 3748
% 0.69/0.85  # ...of these trivial                  : 9
% 0.69/0.85  # ...subsumed                          : 2682
% 0.69/0.85  # ...remaining for further processing  : 1057
% 0.69/0.85  # Other redundant clauses eliminated   : 14
% 0.69/0.85  # Clauses deleted for lack of memory   : 0
% 0.69/0.85  # Backward-subsumed                    : 120
% 0.69/0.85  # Backward-rewritten                   : 257
% 0.69/0.85  # Generated clauses                    : 36715
% 0.69/0.85  # ...of the previous two non-trivial   : 33734
% 0.69/0.85  # Contextual simplify-reflections      : 57
% 0.69/0.85  # Paramodulations                      : 36606
% 0.69/0.85  # Factorizations                       : 96
% 0.69/0.85  # Equation resolutions                 : 14
% 0.69/0.85  # Propositional unsat checks           : 0
% 0.69/0.85  #    Propositional check models        : 0
% 0.69/0.85  #    Propositional check unsatisfiable : 0
% 0.69/0.85  #    Propositional clauses             : 0
% 0.69/0.85  #    Propositional clauses after purity: 0
% 0.69/0.85  #    Propositional unsat core size     : 0
% 0.69/0.85  #    Propositional preprocessing time  : 0.000
% 0.69/0.85  #    Propositional encoding time       : 0.000
% 0.69/0.85  #    Propositional solver time         : 0.000
% 0.69/0.85  #    Success case prop preproc time    : 0.000
% 0.69/0.85  #    Success case prop encoding time   : 0.000
% 0.69/0.85  #    Success case prop solver time     : 0.000
% 0.69/0.85  # Current number of processed clauses  : 635
% 0.69/0.85  #    Positive orientable unit clauses  : 32
% 0.69/0.85  #    Positive unorientable unit clauses: 0
% 0.69/0.85  #    Negative unit clauses             : 7
% 0.69/0.85  #    Non-unit-clauses                  : 596
% 0.69/0.85  # Current number of unprocessed clauses: 29032
% 0.69/0.85  # ...number of literals in the above   : 125616
% 0.69/0.85  # Current number of archived formulas  : 0
% 0.69/0.85  # Current number of archived clauses   : 417
% 0.69/0.85  # Clause-clause subsumption calls (NU) : 67082
% 0.69/0.85  # Rec. Clause-clause subsumption calls : 33507
% 0.69/0.85  # Non-unit clause-clause subsumptions  : 1560
% 0.69/0.85  # Unit Clause-clause subsumption calls : 2236
% 0.69/0.85  # Rewrite failures with RHS unbound    : 0
% 0.69/0.85  # BW rewrite match attempts            : 65
% 0.69/0.85  # BW rewrite match successes           : 19
% 0.69/0.85  # Condensation attempts                : 0
% 0.69/0.85  # Condensation successes               : 0
% 0.69/0.85  # Termbank termtop insertions          : 748810
% 0.69/0.85  
% 0.69/0.85  # -------------------------------------------------
% 0.69/0.85  # User time                : 0.479 s
% 0.69/0.85  # System time              : 0.021 s
% 0.69/0.85  # Total time               : 0.500 s
% 0.69/0.85  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
