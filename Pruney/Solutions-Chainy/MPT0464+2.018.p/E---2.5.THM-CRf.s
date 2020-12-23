%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:39 EST 2020

% Result     : Theorem 43.20s
% Output     : CNFRefutation 43.20s
% Verified   : 
% Statistics : Number of formulae       :  116 (1328 expanded)
%              Number of clauses        :   70 ( 561 expanded)
%              Number of leaves         :   23 ( 383 expanded)
%              Depth                    :   19
%              Number of atoms          :  277 (2288 expanded)
%              Number of equality atoms :   93 (1620 expanded)
%              Maximal formula depth    :   32 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(d3_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( X6 = k3_enumset1(X1,X2,X3,X4,X5)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X7 != X1
              & X7 != X2
              & X7 != X3
              & X7 != X4
              & X7 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(t7_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ( X1 = k1_xboole_0
        | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t48_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( r1_tarski(X1,X2)
               => r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(c_0_23,plain,(
    ! [X69,X70] : k1_setfam_1(k2_tarski(X69,X70)) = k3_xboole_0(X69,X70) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_24,plain,(
    ! [X34,X35] : k1_enumset1(X34,X34,X35) = k2_tarski(X34,X35) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X20) = k5_xboole_0(X19,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X30,X31] : r1_xboole_0(k4_xboole_0(X30,X31),X31) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_31,plain,(
    ! [X36,X37,X38] : k2_enumset1(X36,X36,X37,X38) = k1_enumset1(X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_32,plain,(
    ! [X39,X40,X41,X42] : k3_enumset1(X39,X39,X40,X41,X42) = k2_enumset1(X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_33,plain,(
    ! [X43,X44,X45,X46,X47] : k4_enumset1(X43,X43,X44,X45,X46,X47) = k3_enumset1(X43,X44,X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_34,plain,(
    ! [X12] : k3_xboole_0(X12,X12) = X12 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_35,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r1_xboole_0(X13,X14)
        | r2_hidden(esk2_2(X13,X14),k3_xboole_0(X13,X14)) )
      & ( ~ r2_hidden(X18,k3_xboole_0(X16,X17))
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_36,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X32,X33] :
      ( ~ v1_xboole_0(X32)
      | X32 = X33
      | ~ v1_xboole_0(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_43,plain,(
    ! [X54,X55,X56,X57,X58,X59,X60,X61,X62,X63,X64,X65,X66,X67] :
      ( ( ~ r2_hidden(X60,X59)
        | X60 = X54
        | X60 = X55
        | X60 = X56
        | X60 = X57
        | X60 = X58
        | X59 != k3_enumset1(X54,X55,X56,X57,X58) )
      & ( X61 != X54
        | r2_hidden(X61,X59)
        | X59 != k3_enumset1(X54,X55,X56,X57,X58) )
      & ( X61 != X55
        | r2_hidden(X61,X59)
        | X59 != k3_enumset1(X54,X55,X56,X57,X58) )
      & ( X61 != X56
        | r2_hidden(X61,X59)
        | X59 != k3_enumset1(X54,X55,X56,X57,X58) )
      & ( X61 != X57
        | r2_hidden(X61,X59)
        | X59 != k3_enumset1(X54,X55,X56,X57,X58) )
      & ( X61 != X58
        | r2_hidden(X61,X59)
        | X59 != k3_enumset1(X54,X55,X56,X57,X58) )
      & ( esk3_6(X62,X63,X64,X65,X66,X67) != X62
        | ~ r2_hidden(esk3_6(X62,X63,X64,X65,X66,X67),X67)
        | X67 = k3_enumset1(X62,X63,X64,X65,X66) )
      & ( esk3_6(X62,X63,X64,X65,X66,X67) != X63
        | ~ r2_hidden(esk3_6(X62,X63,X64,X65,X66,X67),X67)
        | X67 = k3_enumset1(X62,X63,X64,X65,X66) )
      & ( esk3_6(X62,X63,X64,X65,X66,X67) != X64
        | ~ r2_hidden(esk3_6(X62,X63,X64,X65,X66,X67),X67)
        | X67 = k3_enumset1(X62,X63,X64,X65,X66) )
      & ( esk3_6(X62,X63,X64,X65,X66,X67) != X65
        | ~ r2_hidden(esk3_6(X62,X63,X64,X65,X66,X67),X67)
        | X67 = k3_enumset1(X62,X63,X64,X65,X66) )
      & ( esk3_6(X62,X63,X64,X65,X66,X67) != X66
        | ~ r2_hidden(esk3_6(X62,X63,X64,X65,X66,X67),X67)
        | X67 = k3_enumset1(X62,X63,X64,X65,X66) )
      & ( r2_hidden(esk3_6(X62,X63,X64,X65,X66,X67),X67)
        | esk3_6(X62,X63,X64,X65,X66,X67) = X62
        | esk3_6(X62,X63,X64,X65,X66,X67) = X63
        | esk3_6(X62,X63,X64,X65,X66,X67) = X64
        | esk3_6(X62,X63,X64,X65,X66,X67) = X65
        | esk3_6(X62,X63,X64,X65,X66,X67) = X66
        | X67 = k3_enumset1(X62,X63,X64,X65,X66) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).

fof(c_0_44,plain,(
    ! [X26,X27] :
      ( ~ r1_tarski(X26,X27)
      | k3_xboole_0(X26,X27) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_45,plain,(
    ! [X28,X29] : r1_tarski(k4_xboole_0(X28,X29),X28) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_30]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_49,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_51,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_52,plain,(
    ! [X48,X49,X50] :
      ( ( r2_hidden(X48,X50)
        | ~ r1_tarski(k2_tarski(X48,X49),X50) )
      & ( r2_hidden(X49,X50)
        | ~ r1_tarski(k2_tarski(X48,X49),X50) )
      & ( ~ r2_hidden(X48,X50)
        | ~ r2_hidden(X49,X50)
        | r1_tarski(k2_tarski(X48,X49),X50) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X5,X6,X7,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_54,plain,(
    ! [X51,X52,X53] :
      ( ( ~ r2_hidden(X51,X53)
        | k4_xboole_0(k2_tarski(X51,X52),X53) != k2_tarski(X51,X52) )
      & ( ~ r2_hidden(X52,X53)
        | k4_xboole_0(k2_tarski(X51,X52),X53) != k2_tarski(X51,X52) )
      & ( r2_hidden(X51,X53)
        | r2_hidden(X52,X53)
        | k4_xboole_0(k2_tarski(X51,X52),X53) = k2_tarski(X51,X52) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_30]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_58,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X4,X5,X6,X7,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_40])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k2_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_30]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_65,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,k1_setfam_1(k4_enumset1(k5_xboole_0(X2,X2),k5_xboole_0(X2,X2),k5_xboole_0(X2,X2),k5_xboole_0(X2,X2),k5_xboole_0(X2,X2),X2))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_67,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_69,plain,
    ( r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_27]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k4_enumset1(X2,X2,X3,X4,X5,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_62])])).

cnf(c_0_71,plain,
    ( k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X1),k1_setfam_1(k4_enumset1(k4_enumset1(X3,X3,X3,X3,X3,X1),k4_enumset1(X3,X3,X3,X3,X3,X1),k4_enumset1(X3,X3,X3,X3,X3,X1),k4_enumset1(X3,X3,X3,X3,X3,X1),k4_enumset1(X3,X3,X3,X3,X3,X1),X2))) != k4_enumset1(X3,X3,X3,X3,X3,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_27]),c_0_27]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_72,plain,
    ( k1_setfam_1(k4_enumset1(k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),X1)) = k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_73,plain,
    ( k1_setfam_1(k4_enumset1(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X2,X2,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_68,c_0_40])).

fof(c_0_75,plain,(
    ! [X73,X74] :
      ( ~ r1_tarski(X73,X74)
      | X73 = k1_xboole_0
      | r1_tarski(k1_setfam_1(X74),k1_setfam_1(X73)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_setfam_1])])).

cnf(c_0_76,plain,
    ( r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X3,X3,X4,X5,X6,X2))
    | ~ r2_hidden(X1,k4_enumset1(X3,X3,X4,X5,X6,X2)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_77,plain,
    ( k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2)) != k4_enumset1(X1,X1,X1,X1,X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_48]),c_0_70])])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_48]),c_0_73])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,k4_enumset1(X1,X1,X2,X3,X4,X5)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_74])])).

fof(c_0_80,plain,(
    ! [X71,X72] :
      ( ( ~ m1_subset_1(X71,k1_zfmisc_1(X72))
        | r1_tarski(X71,X72) )
      & ( ~ r1_tarski(X71,X72)
        | m1_subset_1(X71,k1_zfmisc_1(X72)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_81,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_82,plain,
    ( r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X3,X4,X5,X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_70])).

cnf(c_0_83,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,plain,
    ( r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X2,X2,X3,X4,X5,X6))
    | ~ r2_hidden(X1,k4_enumset1(X2,X2,X3,X4,X5,X6)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_79])).

fof(c_0_85,plain,(
    ! [X75,X76] :
      ( ~ v1_relat_1(X75)
      | ~ m1_subset_1(X76,k1_zfmisc_1(X75))
      | v1_relat_1(X76) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_86,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_87,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5)),X5) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_48]),c_0_83])).

cnf(c_0_88,plain,
    ( r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X2,X3,X4,X5)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_79])).

fof(c_0_89,plain,(
    ! [X77,X78,X79] :
      ( ~ v1_relat_1(X77)
      | ~ v1_relat_1(X78)
      | ~ v1_relat_1(X79)
      | ~ r1_tarski(X77,X78)
      | r1_tarski(k5_relat_1(X79,X77),k5_relat_1(X79,X78)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).

cnf(c_0_90,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_91,plain,
    ( m1_subset_1(k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5)),k1_zfmisc_1(X5)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

fof(c_0_92,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

cnf(c_0_93,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5)),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_88]),c_0_48]),c_0_83])).

cnf(c_0_94,plain,
    ( r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_95,plain,
    ( v1_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5)))
    | ~ v1_relat_1(X5) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

fof(c_0_96,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_relat_1(esk5_0)
    & v1_relat_1(esk6_0)
    & ~ r1_tarski(k5_relat_1(esk4_0,k3_xboole_0(esk5_0,esk6_0)),k3_xboole_0(k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_92])])])).

cnf(c_0_97,plain,
    ( m1_subset_1(k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_93])).

fof(c_0_98,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,X24)
      | ~ r1_tarski(X23,X25)
      | r1_tarski(X23,k3_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_99,plain,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k4_enumset1(X2,X2,X3,X4,X5,X6))),k5_relat_1(X1,X6))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X6) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_87]),c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_101,plain,
    ( v1_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_97])).

cnf(c_0_102,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k4_enumset1(X2,X2,X3,X4,X5,esk6_0))),k5_relat_1(X1,esk6_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_105,plain,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k4_enumset1(X2,X2,X3,X4,X5,X6))),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_93]),c_0_101])).

cnf(c_0_106,plain,
    ( r1_tarski(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_30]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk4_0,k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,esk6_0))),k5_relat_1(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk4_0,k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5))),k5_relat_1(esk4_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_104])).

cnf(c_0_109,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_110,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk4_0,k3_xboole_0(esk5_0,esk6_0)),k3_xboole_0(k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk4_0,k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,esk6_0))),k1_setfam_1(k4_enumset1(X5,X5,X5,X5,X5,k5_relat_1(esk4_0,esk6_0))))
    | ~ r1_tarski(k5_relat_1(esk4_0,k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,esk6_0))),X5) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk4_0,k1_setfam_1(k4_enumset1(esk5_0,esk5_0,X1,X2,X3,X4))),k5_relat_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_113,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk4_0,k1_setfam_1(k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))),k1_setfam_1(k4_enumset1(k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_30]),c_0_30]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk4_0,k1_setfam_1(k4_enumset1(esk5_0,esk5_0,X1,X2,X3,esk6_0))),k1_setfam_1(k4_enumset1(k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_115,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_114])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:34:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 43.20/43.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 43.20/43.44  # and selection function SelectCQArNTNpEqFirst.
% 43.20/43.44  #
% 43.20/43.44  # Preprocessing time       : 0.030 s
% 43.20/43.44  # Presaturation interreduction done
% 43.20/43.44  
% 43.20/43.44  # Proof found!
% 43.20/43.44  # SZS status Theorem
% 43.20/43.44  # SZS output start CNFRefutation
% 43.20/43.44  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 43.20/43.44  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 43.20/43.44  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 43.20/43.44  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 43.20/43.44  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 43.20/43.44  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 43.20/43.44  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 43.20/43.44  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 43.20/43.44  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 43.20/43.44  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 43.20/43.44  fof(d3_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:(X6=k3_enumset1(X1,X2,X3,X4,X5)<=>![X7]:(r2_hidden(X7,X6)<=>~(((((X7!=X1&X7!=X2)&X7!=X3)&X7!=X4)&X7!=X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 43.20/43.44  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 43.20/43.44  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 43.20/43.44  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 43.20/43.44  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 43.20/43.44  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 43.20/43.44  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 43.20/43.44  fof(t7_setfam_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>(X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 43.20/43.44  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 43.20/43.44  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 43.20/43.44  fof(t48_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 43.20/43.44  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 43.20/43.44  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 43.20/43.44  fof(c_0_23, plain, ![X69, X70]:k1_setfam_1(k2_tarski(X69,X70))=k3_xboole_0(X69,X70), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 43.20/43.44  fof(c_0_24, plain, ![X34, X35]:k1_enumset1(X34,X34,X35)=k2_tarski(X34,X35), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 43.20/43.44  fof(c_0_25, plain, ![X19, X20]:k4_xboole_0(X19,X20)=k5_xboole_0(X19,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 43.20/43.44  cnf(c_0_26, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 43.20/43.44  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 43.20/43.44  fof(c_0_28, plain, ![X30, X31]:r1_xboole_0(k4_xboole_0(X30,X31),X31), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 43.20/43.44  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 43.20/43.44  cnf(c_0_30, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 43.20/43.44  fof(c_0_31, plain, ![X36, X37, X38]:k2_enumset1(X36,X36,X37,X38)=k1_enumset1(X36,X37,X38), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 43.20/43.44  fof(c_0_32, plain, ![X39, X40, X41, X42]:k3_enumset1(X39,X39,X40,X41,X42)=k2_enumset1(X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 43.20/43.44  fof(c_0_33, plain, ![X43, X44, X45, X46, X47]:k4_enumset1(X43,X43,X44,X45,X46,X47)=k3_enumset1(X43,X44,X45,X46,X47), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 43.20/43.44  fof(c_0_34, plain, ![X12]:k3_xboole_0(X12,X12)=X12, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 43.20/43.44  fof(c_0_35, plain, ![X13, X14, X16, X17, X18]:((r1_xboole_0(X13,X14)|r2_hidden(esk2_2(X13,X14),k3_xboole_0(X13,X14)))&(~r2_hidden(X18,k3_xboole_0(X16,X17))|~r1_xboole_0(X16,X17))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 43.20/43.44  cnf(c_0_36, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 43.20/43.44  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 43.20/43.44  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 43.20/43.44  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 43.20/43.44  cnf(c_0_40, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 43.20/43.44  cnf(c_0_41, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 43.20/43.44  fof(c_0_42, plain, ![X32, X33]:(~v1_xboole_0(X32)|X32=X33|~v1_xboole_0(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 43.20/43.44  fof(c_0_43, plain, ![X54, X55, X56, X57, X58, X59, X60, X61, X62, X63, X64, X65, X66, X67]:(((~r2_hidden(X60,X59)|(X60=X54|X60=X55|X60=X56|X60=X57|X60=X58)|X59!=k3_enumset1(X54,X55,X56,X57,X58))&(((((X61!=X54|r2_hidden(X61,X59)|X59!=k3_enumset1(X54,X55,X56,X57,X58))&(X61!=X55|r2_hidden(X61,X59)|X59!=k3_enumset1(X54,X55,X56,X57,X58)))&(X61!=X56|r2_hidden(X61,X59)|X59!=k3_enumset1(X54,X55,X56,X57,X58)))&(X61!=X57|r2_hidden(X61,X59)|X59!=k3_enumset1(X54,X55,X56,X57,X58)))&(X61!=X58|r2_hidden(X61,X59)|X59!=k3_enumset1(X54,X55,X56,X57,X58))))&((((((esk3_6(X62,X63,X64,X65,X66,X67)!=X62|~r2_hidden(esk3_6(X62,X63,X64,X65,X66,X67),X67)|X67=k3_enumset1(X62,X63,X64,X65,X66))&(esk3_6(X62,X63,X64,X65,X66,X67)!=X63|~r2_hidden(esk3_6(X62,X63,X64,X65,X66,X67),X67)|X67=k3_enumset1(X62,X63,X64,X65,X66)))&(esk3_6(X62,X63,X64,X65,X66,X67)!=X64|~r2_hidden(esk3_6(X62,X63,X64,X65,X66,X67),X67)|X67=k3_enumset1(X62,X63,X64,X65,X66)))&(esk3_6(X62,X63,X64,X65,X66,X67)!=X65|~r2_hidden(esk3_6(X62,X63,X64,X65,X66,X67),X67)|X67=k3_enumset1(X62,X63,X64,X65,X66)))&(esk3_6(X62,X63,X64,X65,X66,X67)!=X66|~r2_hidden(esk3_6(X62,X63,X64,X65,X66,X67),X67)|X67=k3_enumset1(X62,X63,X64,X65,X66)))&(r2_hidden(esk3_6(X62,X63,X64,X65,X66,X67),X67)|(esk3_6(X62,X63,X64,X65,X66,X67)=X62|esk3_6(X62,X63,X64,X65,X66,X67)=X63|esk3_6(X62,X63,X64,X65,X66,X67)=X64|esk3_6(X62,X63,X64,X65,X66,X67)=X65|esk3_6(X62,X63,X64,X65,X66,X67)=X66)|X67=k3_enumset1(X62,X63,X64,X65,X66)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).
% 43.20/43.44  fof(c_0_44, plain, ![X26, X27]:(~r1_tarski(X26,X27)|k3_xboole_0(X26,X27)=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 43.20/43.44  fof(c_0_45, plain, ![X28, X29]:r1_tarski(k4_xboole_0(X28,X29),X28), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 43.20/43.44  cnf(c_0_46, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 43.20/43.44  cnf(c_0_47, plain, (r1_xboole_0(k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 43.20/43.44  cnf(c_0_48, plain, (k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_30]), c_0_38]), c_0_39]), c_0_40])).
% 43.20/43.44  cnf(c_0_49, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 43.20/43.44  cnf(c_0_50, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 43.20/43.44  fof(c_0_51, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 43.20/43.44  fof(c_0_52, plain, ![X48, X49, X50]:(((r2_hidden(X48,X50)|~r1_tarski(k2_tarski(X48,X49),X50))&(r2_hidden(X49,X50)|~r1_tarski(k2_tarski(X48,X49),X50)))&(~r2_hidden(X48,X50)|~r2_hidden(X49,X50)|r1_tarski(k2_tarski(X48,X49),X50))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 43.20/43.44  cnf(c_0_53, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X5,X6,X7,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 43.20/43.44  fof(c_0_54, plain, ![X51, X52, X53]:(((~r2_hidden(X51,X53)|k4_xboole_0(k2_tarski(X51,X52),X53)!=k2_tarski(X51,X52))&(~r2_hidden(X52,X53)|k4_xboole_0(k2_tarski(X51,X52),X53)!=k2_tarski(X51,X52)))&(r2_hidden(X51,X53)|r2_hidden(X52,X53)|k4_xboole_0(k2_tarski(X51,X52),X53)=k2_tarski(X51,X52))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 43.20/43.44  cnf(c_0_55, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 43.20/43.44  cnf(c_0_56, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 43.20/43.44  cnf(c_0_57, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_30]), c_0_38]), c_0_39]), c_0_40])).
% 43.20/43.44  cnf(c_0_58, plain, (r1_xboole_0(k5_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 43.20/43.44  cnf(c_0_59, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 43.20/43.44  cnf(c_0_60, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 43.20/43.44  cnf(c_0_61, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 43.20/43.44  cnf(c_0_62, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X4,X5,X6,X7,X2)), inference(rw,[status(thm)],[c_0_53, c_0_40])).
% 43.20/43.44  cnf(c_0_63, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)!=k2_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 43.20/43.44  cnf(c_0_64, plain, (k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_30]), c_0_38]), c_0_39]), c_0_40])).
% 43.20/43.44  cnf(c_0_65, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 43.20/43.44  cnf(c_0_66, plain, (~r2_hidden(X1,k1_setfam_1(k4_enumset1(k5_xboole_0(X2,X2),k5_xboole_0(X2,X2),k5_xboole_0(X2,X2),k5_xboole_0(X2,X2),k5_xboole_0(X2,X2),X2)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 43.20/43.44  cnf(c_0_67, plain, (k1_xboole_0=X1|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 43.20/43.44  cnf(c_0_68, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 43.20/43.44  cnf(c_0_69, plain, (r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_27]), c_0_38]), c_0_39]), c_0_40])).
% 43.20/43.44  cnf(c_0_70, plain, (r2_hidden(X1,k4_enumset1(X2,X2,X3,X4,X5,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_62])])).
% 43.20/43.44  cnf(c_0_71, plain, (k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X1),k1_setfam_1(k4_enumset1(k4_enumset1(X3,X3,X3,X3,X3,X1),k4_enumset1(X3,X3,X3,X3,X3,X1),k4_enumset1(X3,X3,X3,X3,X3,X1),k4_enumset1(X3,X3,X3,X3,X3,X1),k4_enumset1(X3,X3,X3,X3,X3,X1),X2)))!=k4_enumset1(X3,X3,X3,X3,X3,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_27]), c_0_27]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 43.20/43.44  cnf(c_0_72, plain, (k1_setfam_1(k4_enumset1(k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),X1))=k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 43.20/43.44  cnf(c_0_73, plain, (k1_setfam_1(k4_enumset1(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 43.20/43.44  cnf(c_0_74, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X2,X2,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_68, c_0_40])).
% 43.20/43.44  fof(c_0_75, plain, ![X73, X74]:(~r1_tarski(X73,X74)|(X73=k1_xboole_0|r1_tarski(k1_setfam_1(X74),k1_setfam_1(X73)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_setfam_1])])).
% 43.20/43.44  cnf(c_0_76, plain, (r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X3,X3,X4,X5,X6,X2))|~r2_hidden(X1,k4_enumset1(X3,X3,X4,X5,X6,X2))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 43.20/43.44  cnf(c_0_77, plain, (k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2))!=k4_enumset1(X1,X1,X1,X1,X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_48]), c_0_70])])).
% 43.20/43.44  cnf(c_0_78, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_48]), c_0_73])).
% 43.20/43.44  cnf(c_0_79, plain, (r2_hidden(X1,k4_enumset1(X1,X1,X2,X3,X4,X5))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_74])])).
% 43.20/43.44  fof(c_0_80, plain, ![X71, X72]:((~m1_subset_1(X71,k1_zfmisc_1(X72))|r1_tarski(X71,X72))&(~r1_tarski(X71,X72)|m1_subset_1(X71,k1_zfmisc_1(X72)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 43.20/43.44  cnf(c_0_81, plain, (X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 43.20/43.44  cnf(c_0_82, plain, (r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X3,X4,X5,X1))), inference(spm,[status(thm)],[c_0_76, c_0_70])).
% 43.20/43.44  cnf(c_0_83, plain, (k4_enumset1(X1,X1,X1,X1,X1,X2)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_77, c_0_78])).
% 43.20/43.44  cnf(c_0_84, plain, (r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X2,X2,X3,X4,X5,X6))|~r2_hidden(X1,k4_enumset1(X2,X2,X3,X4,X5,X6))), inference(spm,[status(thm)],[c_0_69, c_0_79])).
% 43.20/43.44  fof(c_0_85, plain, ![X75, X76]:(~v1_relat_1(X75)|(~m1_subset_1(X76,k1_zfmisc_1(X75))|v1_relat_1(X76))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 43.20/43.44  cnf(c_0_86, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 43.20/43.44  cnf(c_0_87, plain, (r1_tarski(k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5)),X5)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_48]), c_0_83])).
% 43.20/43.44  cnf(c_0_88, plain, (r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X2,X3,X4,X5))), inference(spm,[status(thm)],[c_0_84, c_0_79])).
% 43.20/43.44  fof(c_0_89, plain, ![X77, X78, X79]:(~v1_relat_1(X77)|(~v1_relat_1(X78)|(~v1_relat_1(X79)|(~r1_tarski(X77,X78)|r1_tarski(k5_relat_1(X79,X77),k5_relat_1(X79,X78)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).
% 43.20/43.44  cnf(c_0_90, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 43.20/43.44  cnf(c_0_91, plain, (m1_subset_1(k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5)),k1_zfmisc_1(X5))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 43.20/43.44  fof(c_0_92, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 43.20/43.44  cnf(c_0_93, plain, (r1_tarski(k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5)),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_88]), c_0_48]), c_0_83])).
% 43.20/43.44  cnf(c_0_94, plain, (r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 43.20/43.44  cnf(c_0_95, plain, (v1_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5)))|~v1_relat_1(X5)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 43.20/43.44  fof(c_0_96, negated_conjecture, (v1_relat_1(esk4_0)&(v1_relat_1(esk5_0)&(v1_relat_1(esk6_0)&~r1_tarski(k5_relat_1(esk4_0,k3_xboole_0(esk5_0,esk6_0)),k3_xboole_0(k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk6_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_92])])])).
% 43.20/43.44  cnf(c_0_97, plain, (m1_subset_1(k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_86, c_0_93])).
% 43.20/43.44  fof(c_0_98, plain, ![X23, X24, X25]:(~r1_tarski(X23,X24)|~r1_tarski(X23,X25)|r1_tarski(X23,k3_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 43.20/43.44  cnf(c_0_99, plain, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k4_enumset1(X2,X2,X3,X4,X5,X6))),k5_relat_1(X1,X6))|~v1_relat_1(X1)|~v1_relat_1(X6)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_87]), c_0_95])).
% 43.20/43.44  cnf(c_0_100, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 43.20/43.44  cnf(c_0_101, plain, (v1_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_90, c_0_97])).
% 43.20/43.44  cnf(c_0_102, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 43.20/43.44  cnf(c_0_103, negated_conjecture, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k4_enumset1(X2,X2,X3,X4,X5,esk6_0))),k5_relat_1(X1,esk6_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 43.20/43.44  cnf(c_0_104, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 43.20/43.44  cnf(c_0_105, plain, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k4_enumset1(X2,X2,X3,X4,X5,X6))),k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_93]), c_0_101])).
% 43.20/43.44  cnf(c_0_106, plain, (r1_tarski(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_30]), c_0_38]), c_0_39]), c_0_40])).
% 43.20/43.44  cnf(c_0_107, negated_conjecture, (r1_tarski(k5_relat_1(esk4_0,k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,esk6_0))),k5_relat_1(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 43.20/43.44  cnf(c_0_108, negated_conjecture, (r1_tarski(k5_relat_1(esk4_0,k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5))),k5_relat_1(esk4_0,X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_105, c_0_104])).
% 43.20/43.44  cnf(c_0_109, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 43.20/43.44  cnf(c_0_110, negated_conjecture, (~r1_tarski(k5_relat_1(esk4_0,k3_xboole_0(esk5_0,esk6_0)),k3_xboole_0(k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 43.20/43.44  cnf(c_0_111, negated_conjecture, (r1_tarski(k5_relat_1(esk4_0,k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,esk6_0))),k1_setfam_1(k4_enumset1(X5,X5,X5,X5,X5,k5_relat_1(esk4_0,esk6_0))))|~r1_tarski(k5_relat_1(esk4_0,k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,esk6_0))),X5)), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 43.20/43.44  cnf(c_0_112, negated_conjecture, (r1_tarski(k5_relat_1(esk4_0,k1_setfam_1(k4_enumset1(esk5_0,esk5_0,X1,X2,X3,X4))),k5_relat_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 43.20/43.44  cnf(c_0_113, negated_conjecture, (~r1_tarski(k5_relat_1(esk4_0,k1_setfam_1(k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))),k1_setfam_1(k4_enumset1(k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_30]), c_0_30]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40])).
% 43.20/43.44  cnf(c_0_114, negated_conjecture, (r1_tarski(k5_relat_1(esk4_0,k1_setfam_1(k4_enumset1(esk5_0,esk5_0,X1,X2,X3,esk6_0))),k1_setfam_1(k4_enumset1(k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk6_0))))), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 43.20/43.44  cnf(c_0_115, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_114])]), ['proof']).
% 43.20/43.44  # SZS output end CNFRefutation
% 43.20/43.44  # Proof object total steps             : 116
% 43.20/43.44  # Proof object clause steps            : 70
% 43.20/43.44  # Proof object formula steps           : 46
% 43.20/43.44  # Proof object conjectures             : 15
% 43.20/43.44  # Proof object clause conjectures      : 12
% 43.20/43.44  # Proof object formula conjectures     : 3
% 43.20/43.44  # Proof object initial clauses used    : 27
% 43.20/43.44  # Proof object initial formulas used   : 23
% 43.20/43.44  # Proof object generating inferences   : 26
% 43.20/43.44  # Proof object simplifying inferences  : 77
% 43.20/43.44  # Training examples: 0 positive, 0 negative
% 43.20/43.44  # Parsed axioms                        : 24
% 43.20/43.44  # Removed by relevancy pruning/SinE    : 0
% 43.20/43.44  # Initial clauses                      : 45
% 43.20/43.44  # Removed in clause preprocessing      : 6
% 43.20/43.44  # Initial clauses in saturation        : 39
% 43.20/43.44  # Processed clauses                    : 23102
% 43.20/43.44  # ...of these trivial                  : 663
% 43.20/43.44  # ...subsumed                          : 14346
% 43.20/43.44  # ...remaining for further processing  : 8093
% 43.20/43.44  # Other redundant clauses eliminated   : 8154
% 43.20/43.44  # Clauses deleted for lack of memory   : 0
% 43.20/43.44  # Backward-subsumed                    : 193
% 43.20/43.44  # Backward-rewritten                   : 250
% 43.20/43.44  # Generated clauses                    : 1408265
% 43.20/43.44  # ...of the previous two non-trivial   : 1298481
% 43.20/43.44  # Contextual simplify-reflections      : 369
% 43.20/43.44  # Paramodulations                      : 1393967
% 43.20/43.44  # Factorizations                       : 6149
% 43.20/43.44  # Equation resolutions                 : 8154
% 43.20/43.44  # Propositional unsat checks           : 1
% 43.20/43.44  #    Propositional check models        : 0
% 43.20/43.44  #    Propositional check unsatisfiable : 0
% 43.20/43.44  #    Propositional clauses             : 0
% 43.20/43.44  #    Propositional clauses after purity: 0
% 43.20/43.44  #    Propositional unsat core size     : 0
% 43.20/43.44  #    Propositional preprocessing time  : 0.000
% 43.20/43.44  #    Propositional encoding time       : 0.445
% 43.20/43.44  #    Propositional solver time         : 0.057
% 43.20/43.44  #    Success case prop preproc time    : 0.000
% 43.20/43.44  #    Success case prop encoding time   : 0.000
% 43.20/43.44  #    Success case prop solver time     : 0.000
% 43.20/43.44  # Current number of processed clauses  : 7605
% 43.20/43.44  #    Positive orientable unit clauses  : 1575
% 43.20/43.44  #    Positive unorientable unit clauses: 0
% 43.20/43.44  #    Negative unit clauses             : 4
% 43.20/43.44  #    Non-unit-clauses                  : 6026
% 43.20/43.44  # Current number of unprocessed clauses: 1274095
% 43.20/43.44  # ...number of literals in the above   : 13242851
% 43.20/43.44  # Current number of archived formulas  : 0
% 43.20/43.44  # Current number of archived clauses   : 488
% 43.20/43.44  # Clause-clause subsumption calls (NU) : 7705445
% 43.20/43.44  # Rec. Clause-clause subsumption calls : 5162915
% 43.20/43.44  # Non-unit clause-clause subsumptions  : 14349
% 43.20/43.44  # Unit Clause-clause subsumption calls : 683175
% 43.20/43.44  # Rewrite failures with RHS unbound    : 0
% 43.20/43.44  # BW rewrite match attempts            : 105152
% 43.20/43.44  # BW rewrite match successes           : 174
% 43.20/43.44  # Condensation attempts                : 0
% 43.20/43.44  # Condensation successes               : 0
% 43.20/43.44  # Termbank termtop insertions          : 176285643
% 43.30/43.50  
% 43.30/43.50  # -------------------------------------------------
% 43.30/43.50  # User time                : 42.328 s
% 43.30/43.50  # System time              : 0.788 s
% 43.30/43.50  # Total time               : 43.116 s
% 43.30/43.50  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
