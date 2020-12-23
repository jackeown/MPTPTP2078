%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:50 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 258 expanded)
%              Number of clauses        :   47 ( 109 expanded)
%              Number of leaves         :   18 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  175 ( 435 expanded)
%              Number of equality atoms :   55 ( 211 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t2_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( ~ v1_xboole_0(k3_xboole_0(X1,X2))
         => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(c_0_18,plain,(
    ! [X64,X65] : k1_setfam_1(k2_tarski(X64,X65)) = k3_xboole_0(X64,X65) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_19,plain,(
    ! [X37,X38] : k1_enumset1(X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X31,X32] : k4_xboole_0(X31,X32) = k5_xboole_0(X31,k3_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X35,X36] : r1_tarski(k4_xboole_0(X35,X36),X35) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_26,plain,(
    ! [X39,X40,X41] : k2_enumset1(X39,X39,X40,X41) = k1_enumset1(X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X42,X43,X44,X45] : k3_enumset1(X42,X42,X43,X44,X45) = k2_enumset1(X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,plain,(
    ! [X46,X47,X48,X49,X50] : k4_enumset1(X46,X46,X47,X48,X49,X50) = k3_enumset1(X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_29,plain,(
    ! [X51,X52,X53,X54,X55,X56] : k5_enumset1(X51,X51,X52,X53,X54,X55,X56) = k4_enumset1(X51,X52,X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_30,plain,(
    ! [X57,X58,X59,X60,X61,X62,X63] : k6_enumset1(X57,X57,X58,X59,X60,X61,X62,X63) = k5_enumset1(X57,X58,X59,X60,X61,X62,X63) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_31,plain,(
    ! [X27] : k3_xboole_0(X27,X27) = X27 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_32,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_40,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_41,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v1_xboole_0(X1)
          & v1_zfmisc_1(X1) )
       => ! [X2] :
            ( ~ v1_xboole_0(k3_xboole_0(X1,X2))
           => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t2_tex_2])).

fof(c_0_42,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25] :
      ( ( r2_hidden(X21,X18)
        | ~ r2_hidden(X21,X20)
        | X20 != k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X21,X19)
        | ~ r2_hidden(X21,X20)
        | X20 != k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X22,X18)
        | r2_hidden(X22,X19)
        | r2_hidden(X22,X20)
        | X20 != k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk3_3(X23,X24,X25),X25)
        | ~ r2_hidden(esk3_3(X23,X24,X25),X23)
        | r2_hidden(esk3_3(X23,X24,X25),X24)
        | X25 = k4_xboole_0(X23,X24) )
      & ( r2_hidden(esk3_3(X23,X24,X25),X23)
        | r2_hidden(esk3_3(X23,X24,X25),X25)
        | X25 = k4_xboole_0(X23,X24) )
      & ( ~ r2_hidden(esk3_3(X23,X24,X25),X24)
        | r2_hidden(esk3_3(X23,X24,X25),X25)
        | X25 = k4_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_43,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r1_tarski(X12,X13)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk2_2(X15,X16),X15)
        | r1_tarski(X15,X16) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | r1_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_44,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_45,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_25]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_46,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_48,plain,(
    ! [X28,X29] :
      ( ( ~ r2_hidden(esk4_2(X28,X29),X28)
        | ~ r2_hidden(esk4_2(X28,X29),X29)
        | X28 = X29 )
      & ( r2_hidden(esk4_2(X28,X29),X28)
        | r2_hidden(esk4_2(X28,X29),X29)
        | X28 = X29 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_49,plain,(
    ! [X68,X69] :
      ( v1_xboole_0(X68)
      | v1_xboole_0(X69)
      | ~ v1_zfmisc_1(X69)
      | ~ r1_tarski(X68,X69)
      | X68 = X69 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

fof(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0)
    & v1_zfmisc_1(esk5_0)
    & ~ v1_xboole_0(k3_xboole_0(esk5_0,esk6_0))
    & ~ r1_tarski(esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_41])])])])).

fof(c_0_51,plain,(
    ! [X33,X34] : r1_tarski(k3_xboole_0(X33,X34),X33) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r2_hidden(esk4_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( v1_zfmisc_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( X3 != k5_xboole_0(X4,k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk4_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X4 != k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(k3_xboole_0(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_67,negated_conjecture,
    ( X1 = esk5_0
    | v1_xboole_0(X1)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_25]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0
    | r2_hidden(esk4_2(k1_xboole_0,k5_xboole_0(X1,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_72,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_xboole_0(k1_setfam_1(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_25]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_74,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1)) = esk5_0
    | v1_xboole_0(k1_setfam_1(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0
    | ~ r2_hidden(esk4_2(k1_xboole_0,k5_xboole_0(X1,X1)),k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))))
    | r2_hidden(esk2_2(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_45]),c_0_64])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | r2_hidden(esk2_2(esk5_0,X1),esk6_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_55])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.19/0.40  # and selection function GSelectMinInfpos.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.028 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.40  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.40  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.41  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.41  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.41  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.41  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.41  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.41  fof(t2_tex_2, conjecture, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(~(v1_xboole_0(k3_xboole_0(X1,X2)))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 0.19/0.41  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.41  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.41  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 0.19/0.41  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.19/0.41  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.41  fof(c_0_18, plain, ![X64, X65]:k1_setfam_1(k2_tarski(X64,X65))=k3_xboole_0(X64,X65), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.41  fof(c_0_19, plain, ![X37, X38]:k1_enumset1(X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.41  fof(c_0_20, plain, ![X31, X32]:k4_xboole_0(X31,X32)=k5_xboole_0(X31,k3_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.41  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  fof(c_0_23, plain, ![X35, X36]:r1_tarski(k4_xboole_0(X35,X36),X35), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.41  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_25, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.41  fof(c_0_26, plain, ![X39, X40, X41]:k2_enumset1(X39,X39,X40,X41)=k1_enumset1(X39,X40,X41), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.41  fof(c_0_27, plain, ![X42, X43, X44, X45]:k3_enumset1(X42,X42,X43,X44,X45)=k2_enumset1(X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.41  fof(c_0_28, plain, ![X46, X47, X48, X49, X50]:k4_enumset1(X46,X46,X47,X48,X49,X50)=k3_enumset1(X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.41  fof(c_0_29, plain, ![X51, X52, X53, X54, X55, X56]:k5_enumset1(X51,X51,X52,X53,X54,X55,X56)=k4_enumset1(X51,X52,X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.41  fof(c_0_30, plain, ![X57, X58, X59, X60, X61, X62, X63]:k6_enumset1(X57,X57,X58,X59,X60,X61,X62,X63)=k5_enumset1(X57,X58,X59,X60,X61,X62,X63), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.41  fof(c_0_31, plain, ![X27]:k3_xboole_0(X27,X27)=X27, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.41  cnf(c_0_32, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.41  cnf(c_0_33, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.41  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.41  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_36, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_37, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_38, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_39, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  fof(c_0_40, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.41  fof(c_0_41, negated_conjecture, ~(![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(~(v1_xboole_0(k3_xboole_0(X1,X2)))=>r1_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t2_tex_2])).
% 0.19/0.41  fof(c_0_42, plain, ![X18, X19, X20, X21, X22, X23, X24, X25]:((((r2_hidden(X21,X18)|~r2_hidden(X21,X20)|X20!=k4_xboole_0(X18,X19))&(~r2_hidden(X21,X19)|~r2_hidden(X21,X20)|X20!=k4_xboole_0(X18,X19)))&(~r2_hidden(X22,X18)|r2_hidden(X22,X19)|r2_hidden(X22,X20)|X20!=k4_xboole_0(X18,X19)))&((~r2_hidden(esk3_3(X23,X24,X25),X25)|(~r2_hidden(esk3_3(X23,X24,X25),X23)|r2_hidden(esk3_3(X23,X24,X25),X24))|X25=k4_xboole_0(X23,X24))&((r2_hidden(esk3_3(X23,X24,X25),X23)|r2_hidden(esk3_3(X23,X24,X25),X25)|X25=k4_xboole_0(X23,X24))&(~r2_hidden(esk3_3(X23,X24,X25),X24)|r2_hidden(esk3_3(X23,X24,X25),X25)|X25=k4_xboole_0(X23,X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.41  fof(c_0_43, plain, ![X12, X13, X14, X15, X16]:((~r1_tarski(X12,X13)|(~r2_hidden(X14,X12)|r2_hidden(X14,X13)))&((r2_hidden(esk2_2(X15,X16),X15)|r1_tarski(X15,X16))&(~r2_hidden(esk2_2(X15,X16),X16)|r1_tarski(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.41  cnf(c_0_44, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.19/0.41  cnf(c_0_45, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_25]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.19/0.41  cnf(c_0_46, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.41  cnf(c_0_47, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.41  fof(c_0_48, plain, ![X28, X29]:((~r2_hidden(esk4_2(X28,X29),X28)|~r2_hidden(esk4_2(X28,X29),X29)|X28=X29)&(r2_hidden(esk4_2(X28,X29),X28)|r2_hidden(esk4_2(X28,X29),X29)|X28=X29)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.19/0.41  fof(c_0_49, plain, ![X68, X69]:(v1_xboole_0(X68)|(v1_xboole_0(X69)|~v1_zfmisc_1(X69)|(~r1_tarski(X68,X69)|X68=X69))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.19/0.41  fof(c_0_50, negated_conjecture, ((~v1_xboole_0(esk5_0)&v1_zfmisc_1(esk5_0))&(~v1_xboole_0(k3_xboole_0(esk5_0,esk6_0))&~r1_tarski(esk5_0,esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_41])])])])).
% 0.19/0.41  fof(c_0_51, plain, ![X33, X34]:r1_tarski(k3_xboole_0(X33,X34),X33), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.41  cnf(c_0_52, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.41  cnf(c_0_53, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.41  cnf(c_0_54, plain, (r1_tarski(k5_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.41  cnf(c_0_55, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.41  cnf(c_0_56, plain, (r2_hidden(esk4_2(X1,X2),X1)|r2_hidden(esk4_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.41  cnf(c_0_57, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.41  cnf(c_0_58, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (v1_zfmisc_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.41  cnf(c_0_61, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.41  cnf(c_0_62, plain, (X3!=k5_xboole_0(X4,k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.19/0.41  cnf(c_0_63, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.41  cnf(c_0_64, plain, (k1_xboole_0=X1|r2_hidden(esk4_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.41  cnf(c_0_65, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X4!=k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.19/0.41  cnf(c_0_66, negated_conjecture, (~v1_xboole_0(k3_xboole_0(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.41  cnf(c_0_67, negated_conjecture, (X1=esk5_0|v1_xboole_0(X1)|~r1_tarski(X1,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.19/0.41  cnf(c_0_68, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_25]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.19/0.41  cnf(c_0_69, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_62])).
% 0.19/0.41  cnf(c_0_70, plain, (k5_xboole_0(X1,X1)=k1_xboole_0|r2_hidden(esk4_2(k1_xboole_0,k5_xboole_0(X1,X1)),X1)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.41  cnf(c_0_71, plain, (r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_65])).
% 0.19/0.41  cnf(c_0_72, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.41  cnf(c_0_73, negated_conjecture, (~v1_xboole_0(k1_setfam_1(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_25]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.19/0.41  cnf(c_0_74, negated_conjecture, (k1_setfam_1(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1))=esk5_0|v1_xboole_0(k1_setfam_1(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1)))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.41  cnf(c_0_75, plain, (k5_xboole_0(X1,X1)=k1_xboole_0|~r2_hidden(esk4_2(k1_xboole_0,k5_xboole_0(X1,X1)),k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.41  cnf(c_0_76, plain, (r1_tarski(X1,X2)|r2_hidden(esk2_2(X1,X2),k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))))|r2_hidden(esk2_2(X1,X2),X3)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.19/0.41  cnf(c_0_77, negated_conjecture, (k1_setfam_1(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))=esk5_0), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.41  cnf(c_0_78, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_45]), c_0_64])).
% 0.19/0.41  cnf(c_0_79, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.41  cnf(c_0_80, negated_conjecture, (r1_tarski(esk5_0,X1)|r2_hidden(esk2_2(esk5_0,X1),esk6_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_55])).
% 0.19/0.41  cnf(c_0_81, negated_conjecture, (~r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.41  cnf(c_0_82, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 83
% 0.19/0.41  # Proof object clause steps            : 47
% 0.19/0.41  # Proof object formula steps           : 36
% 0.19/0.41  # Proof object conjectures             : 13
% 0.19/0.41  # Proof object clause conjectures      : 10
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 24
% 0.19/0.41  # Proof object initial formulas used   : 18
% 0.19/0.41  # Proof object generating inferences   : 13
% 0.19/0.41  # Proof object simplifying inferences  : 45
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 19
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 31
% 0.19/0.41  # Removed in clause preprocessing      : 8
% 0.19/0.41  # Initial clauses in saturation        : 23
% 0.19/0.41  # Processed clauses                    : 293
% 0.19/0.41  # ...of these trivial                  : 1
% 0.19/0.41  # ...subsumed                          : 141
% 0.19/0.41  # ...remaining for further processing  : 151
% 0.19/0.41  # Other redundant clauses eliminated   : 3
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 2
% 0.19/0.41  # Backward-rewritten                   : 21
% 0.19/0.41  # Generated clauses                    : 1138
% 0.19/0.41  # ...of the previous two non-trivial   : 1029
% 0.19/0.41  # Contextual simplify-reflections      : 5
% 0.19/0.41  # Paramodulations                      : 1118
% 0.19/0.41  # Factorizations                       : 17
% 0.19/0.41  # Equation resolutions                 : 3
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 102
% 0.19/0.41  #    Positive orientable unit clauses  : 9
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 6
% 0.19/0.41  #    Non-unit-clauses                  : 87
% 0.19/0.41  # Current number of unprocessed clauses: 756
% 0.19/0.41  # ...number of literals in the above   : 2768
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 54
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 910
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 597
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 67
% 0.19/0.41  # Unit Clause-clause subsumption calls : 26
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 21
% 0.19/0.41  # BW rewrite match successes           : 6
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 23678
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.057 s
% 0.19/0.41  # System time              : 0.006 s
% 0.19/0.41  # Total time               : 0.063 s
% 0.19/0.41  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
