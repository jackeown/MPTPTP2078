%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:28 EST 2020

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 479 expanded)
%              Number of clauses        :   57 ( 198 expanded)
%              Number of leaves         :   19 ( 131 expanded)
%              Depth                    :   18
%              Number of atoms          :  270 (1152 expanded)
%              Number of equality atoms :  105 ( 554 expanded)
%              Maximal formula depth    :   47 (   4 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(t8_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(k1_setfam_1(X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

fof(d6_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( X9 = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X10 != X1
              & X10 != X2
              & X10 != X3
              & X10 != X4
              & X10 != X5
              & X10 != X6
              & X10 != X7
              & X10 != X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(t30_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(c_0_19,plain,(
    ! [X51,X52] : k3_tarski(k2_tarski(X51,X52)) = k2_xboole_0(X51,X52) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X90] :
      ( ~ v1_relat_1(X90)
      | k3_relat_1(X90) = k2_xboole_0(k1_relat_1(X90),k2_relat_1(X90)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_22,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X26,X27,X28] : k2_enumset1(X26,X26,X27,X28) = k1_enumset1(X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X29,X30,X31,X32] : k3_enumset1(X29,X29,X30,X31,X32) = k2_enumset1(X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_26,plain,(
    ! [X33,X34,X35,X36,X37] : k4_enumset1(X33,X33,X34,X35,X36,X37) = k3_enumset1(X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_27,plain,(
    ! [X38,X39,X40,X41,X42,X43] : k5_enumset1(X38,X38,X39,X40,X41,X42,X43) = k4_enumset1(X38,X39,X40,X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_28,plain,(
    ! [X44,X45,X46,X47,X48,X49,X50] : k6_enumset1(X44,X44,X45,X46,X47,X48,X49,X50) = k5_enumset1(X44,X45,X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

fof(c_0_30,plain,(
    ! [X19,X20] : r1_tarski(X19,k2_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_31,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_38,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_relat_1(esk7_0)
    & r1_tarski(esk6_0,esk7_0)
    & ~ r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k3_relat_1(X1) = k3_tarski(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_42,plain,(
    ! [X74,X75] : k1_setfam_1(k2_tarski(X74,X75)) = k3_xboole_0(X74,X75) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_43,plain,(
    ! [X91,X92] :
      ( ( r1_tarski(k1_relat_1(X91),k1_relat_1(X92))
        | ~ r1_tarski(X91,X92)
        | ~ v1_relat_1(X92)
        | ~ v1_relat_1(X91) )
      & ( r1_tarski(k2_relat_1(X91),k2_relat_1(X92))
        | ~ r1_tarski(X91,X92)
        | ~ v1_relat_1(X92)
        | ~ v1_relat_1(X91) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_44,plain,(
    ! [X76,X77,X78] :
      ( ~ r2_hidden(X76,X77)
      | ~ r1_tarski(X76,X78)
      | r1_tarski(k1_setfam_1(X77),X78) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( k3_tarski(k6_enumset1(k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),k2_relat_1(esk7_0))) = k3_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_47,plain,(
    ! [X53,X54,X55,X56,X57,X58,X59,X60,X61,X62,X63,X64,X65,X66,X67,X68,X69,X70,X71,X72] :
      ( ( ~ r2_hidden(X62,X61)
        | X62 = X53
        | X62 = X54
        | X62 = X55
        | X62 = X56
        | X62 = X57
        | X62 = X58
        | X62 = X59
        | X62 = X60
        | X61 != k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( X63 != X53
        | r2_hidden(X63,X61)
        | X61 != k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( X63 != X54
        | r2_hidden(X63,X61)
        | X61 != k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( X63 != X55
        | r2_hidden(X63,X61)
        | X61 != k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( X63 != X56
        | r2_hidden(X63,X61)
        | X61 != k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( X63 != X57
        | r2_hidden(X63,X61)
        | X61 != k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( X63 != X58
        | r2_hidden(X63,X61)
        | X61 != k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( X63 != X59
        | r2_hidden(X63,X61)
        | X61 != k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( X63 != X60
        | r2_hidden(X63,X61)
        | X61 != k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60) )
      & ( esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) != X64
        | ~ r2_hidden(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)
        | X72 = k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) != X65
        | ~ r2_hidden(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)
        | X72 = k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) != X66
        | ~ r2_hidden(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)
        | X72 = k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) != X67
        | ~ r2_hidden(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)
        | X72 = k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) != X68
        | ~ r2_hidden(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)
        | X72 = k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) != X69
        | ~ r2_hidden(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)
        | X72 = k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) != X70
        | ~ r2_hidden(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)
        | X72 = k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) != X71
        | ~ r2_hidden(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)
        | X72 = k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) )
      & ( r2_hidden(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)
        | esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) = X64
        | esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) = X65
        | esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) = X66
        | esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) = X67
        | esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) = X68
        | esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) = X69
        | esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) = X70
        | esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72) = X71
        | X72 = k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

fof(c_0_48,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | k3_xboole_0(X17,X18) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_49,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_setfam_1(X2),X3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_49,c_0_23])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_59,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk1_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk1_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_60,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_61,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,X22)
      | ~ r1_tarski(X23,X22)
      | r1_tarski(k2_xboole_0(X21,X23),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k1_setfam_1(X1),k3_relat_1(esk7_0))
    | ~ r2_hidden(k1_relat_1(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).

cnf(c_0_64,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_41]),c_0_58])])).

cnf(c_0_66,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_51])).

cnf(c_0_68,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,k1_relat_1(esk7_0))),k3_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk7_0))) = k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(k1_setfam_1(X3),X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_41]),c_0_58])])).

fof(c_0_73,plain,(
    ! [X79,X80,X81,X83,X84,X85,X86,X88] :
      ( ( ~ r2_hidden(X81,X80)
        | r2_hidden(k4_tarski(esk3_3(X79,X80,X81),X81),X79)
        | X80 != k2_relat_1(X79) )
      & ( ~ r2_hidden(k4_tarski(X84,X83),X79)
        | r2_hidden(X83,X80)
        | X80 != k2_relat_1(X79) )
      & ( ~ r2_hidden(esk4_2(X85,X86),X86)
        | ~ r2_hidden(k4_tarski(X88,esk4_2(X85,X86)),X85)
        | X86 = k2_relat_1(X85) )
      & ( r2_hidden(esk4_2(X85,X86),X86)
        | r2_hidden(k4_tarski(esk5_2(X85,X86),esk4_2(X85,X86)),X85)
        | X86 = k2_relat_1(X85) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_74,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(k1_setfam_1(k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_63])).

cnf(c_0_77,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(k2_relat_1(esk6_0),k2_relat_1(esk6_0),k2_relat_1(esk6_0),k2_relat_1(esk6_0),k2_relat_1(esk6_0),k2_relat_1(esk6_0),k2_relat_1(esk6_0),k2_relat_1(esk7_0))) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_72])).

fof(c_0_78,plain,(
    ! [X93,X94,X95] :
      ( ( r2_hidden(X93,k3_relat_1(X95))
        | ~ r2_hidden(k4_tarski(X93,X94),X95)
        | ~ v1_relat_1(X95) )
      & ( r2_hidden(X94,k3_relat_1(X95))
        | ~ r2_hidden(k4_tarski(X93,X94),X95)
        | ~ v1_relat_1(X95) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_79,plain,
    ( r2_hidden(k4_tarski(esk3_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k3_tarski(k6_enumset1(k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),X1)),k3_relat_1(esk7_0))
    | ~ r1_tarski(X1,k3_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))
    | r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( k3_tarski(k6_enumset1(k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k2_relat_1(esk6_0))) = k3_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_51])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_85,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk7_0),k3_relat_1(esk7_0)),k2_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk7_0))
    | ~ r2_hidden(k4_tarski(X2,X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_41])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),k3_relat_1(esk7_0))),esk1_2(k2_relat_1(esk7_0),k3_relat_1(esk7_0))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk7_0),k3_relat_1(esk7_0)),k3_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),k3_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k1_setfam_1(X1),k3_relat_1(esk7_0))
    | ~ r2_hidden(k2_relat_1(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_91])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,k2_relat_1(esk7_0))),k3_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_63])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_77])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_94]),c_0_82]),c_0_83]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.71/0.87  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002I
% 0.71/0.87  # and selection function SelectNegativeLiterals.
% 0.71/0.87  #
% 0.71/0.87  # Preprocessing time       : 0.042 s
% 0.71/0.87  # Presaturation interreduction done
% 0.71/0.87  
% 0.71/0.87  # Proof found!
% 0.71/0.87  # SZS status Theorem
% 0.71/0.87  # SZS output start CNFRefutation
% 0.71/0.87  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.71/0.87  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.71/0.87  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 0.71/0.87  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.71/0.87  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.71/0.87  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.71/0.87  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.71/0.87  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.71/0.87  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 0.71/0.87  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.71/0.87  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.71/0.87  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.71/0.87  fof(t8_setfam_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(k1_setfam_1(X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_setfam_1)).
% 0.71/0.87  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 0.71/0.87  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.71/0.87  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.71/0.87  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.71/0.87  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.71/0.87  fof(t30_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 0.71/0.87  fof(c_0_19, plain, ![X51, X52]:k3_tarski(k2_tarski(X51,X52))=k2_xboole_0(X51,X52), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.71/0.87  fof(c_0_20, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.71/0.87  fof(c_0_21, plain, ![X90]:(~v1_relat_1(X90)|k3_relat_1(X90)=k2_xboole_0(k1_relat_1(X90),k2_relat_1(X90))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.71/0.87  cnf(c_0_22, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.71/0.87  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.71/0.87  fof(c_0_24, plain, ![X26, X27, X28]:k2_enumset1(X26,X26,X27,X28)=k1_enumset1(X26,X27,X28), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.71/0.87  fof(c_0_25, plain, ![X29, X30, X31, X32]:k3_enumset1(X29,X29,X30,X31,X32)=k2_enumset1(X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.71/0.87  fof(c_0_26, plain, ![X33, X34, X35, X36, X37]:k4_enumset1(X33,X33,X34,X35,X36,X37)=k3_enumset1(X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.71/0.87  fof(c_0_27, plain, ![X38, X39, X40, X41, X42, X43]:k5_enumset1(X38,X38,X39,X40,X41,X42,X43)=k4_enumset1(X38,X39,X40,X41,X42,X43), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.71/0.87  fof(c_0_28, plain, ![X44, X45, X46, X47, X48, X49, X50]:k6_enumset1(X44,X44,X45,X46,X47,X48,X49,X50)=k5_enumset1(X44,X45,X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.71/0.87  fof(c_0_29, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 0.71/0.87  fof(c_0_30, plain, ![X19, X20]:r1_tarski(X19,k2_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.71/0.87  cnf(c_0_31, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.71/0.87  cnf(c_0_32, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.71/0.87  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.71/0.87  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.71/0.87  cnf(c_0_35, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.71/0.87  cnf(c_0_36, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.71/0.87  cnf(c_0_37, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.71/0.87  fof(c_0_38, negated_conjecture, (v1_relat_1(esk6_0)&(v1_relat_1(esk7_0)&(r1_tarski(esk6_0,esk7_0)&~r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.71/0.87  cnf(c_0_39, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.71/0.87  cnf(c_0_40, plain, (k3_relat_1(X1)=k3_tarski(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.71/0.87  cnf(c_0_41, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.71/0.87  fof(c_0_42, plain, ![X74, X75]:k1_setfam_1(k2_tarski(X74,X75))=k3_xboole_0(X74,X75), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.71/0.87  fof(c_0_43, plain, ![X91, X92]:((r1_tarski(k1_relat_1(X91),k1_relat_1(X92))|~r1_tarski(X91,X92)|~v1_relat_1(X92)|~v1_relat_1(X91))&(r1_tarski(k2_relat_1(X91),k2_relat_1(X92))|~r1_tarski(X91,X92)|~v1_relat_1(X92)|~v1_relat_1(X91))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.71/0.87  fof(c_0_44, plain, ![X76, X77, X78]:(~r2_hidden(X76,X77)|~r1_tarski(X76,X78)|r1_tarski(k1_setfam_1(X77),X78)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).
% 0.71/0.87  cnf(c_0_45, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.71/0.87  cnf(c_0_46, negated_conjecture, (k3_tarski(k6_enumset1(k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),k1_relat_1(esk7_0),k2_relat_1(esk7_0)))=k3_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.71/0.87  fof(c_0_47, plain, ![X53, X54, X55, X56, X57, X58, X59, X60, X61, X62, X63, X64, X65, X66, X67, X68, X69, X70, X71, X72]:(((~r2_hidden(X62,X61)|(X62=X53|X62=X54|X62=X55|X62=X56|X62=X57|X62=X58|X62=X59|X62=X60)|X61!=k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60))&((((((((X63!=X53|r2_hidden(X63,X61)|X61!=k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60))&(X63!=X54|r2_hidden(X63,X61)|X61!=k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60)))&(X63!=X55|r2_hidden(X63,X61)|X61!=k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60)))&(X63!=X56|r2_hidden(X63,X61)|X61!=k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60)))&(X63!=X57|r2_hidden(X63,X61)|X61!=k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60)))&(X63!=X58|r2_hidden(X63,X61)|X61!=k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60)))&(X63!=X59|r2_hidden(X63,X61)|X61!=k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60)))&(X63!=X60|r2_hidden(X63,X61)|X61!=k6_enumset1(X53,X54,X55,X56,X57,X58,X59,X60))))&(((((((((esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)!=X64|~r2_hidden(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)|X72=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71))&(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)!=X65|~r2_hidden(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)|X72=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)!=X66|~r2_hidden(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)|X72=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)!=X67|~r2_hidden(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)|X72=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)!=X68|~r2_hidden(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)|X72=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)!=X69|~r2_hidden(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)|X72=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)!=X70|~r2_hidden(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)|X72=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)!=X71|~r2_hidden(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)|X72=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))&(r2_hidden(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72),X72)|(esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)=X64|esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)=X65|esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)=X66|esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)=X67|esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)=X68|esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)=X69|esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)=X70|esk2_9(X64,X65,X66,X67,X68,X69,X70,X71,X72)=X71)|X72=k6_enumset1(X64,X65,X66,X67,X68,X69,X70,X71)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.71/0.87  fof(c_0_48, plain, ![X17, X18]:(~r1_tarski(X17,X18)|k3_xboole_0(X17,X18)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.71/0.87  cnf(c_0_49, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.71/0.87  cnf(c_0_50, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.71/0.87  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.71/0.87  cnf(c_0_52, plain, (r1_tarski(k1_setfam_1(X2),X3)|~r2_hidden(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.71/0.87  cnf(c_0_53, negated_conjecture, (r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.71/0.87  cnf(c_0_54, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.71/0.87  cnf(c_0_55, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.71/0.87  cnf(c_0_56, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_49, c_0_23])).
% 0.71/0.87  cnf(c_0_57, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),k1_relat_1(X1))|~v1_relat_1(X1)|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.71/0.87  cnf(c_0_58, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.71/0.87  fof(c_0_59, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk1_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk1_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.71/0.87  cnf(c_0_60, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.71/0.87  fof(c_0_61, plain, ![X21, X22, X23]:(~r1_tarski(X21,X22)|~r1_tarski(X23,X22)|r1_tarski(k2_xboole_0(X21,X23),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.71/0.87  cnf(c_0_62, negated_conjecture, (r1_tarski(k1_setfam_1(X1),k3_relat_1(esk7_0))|~r2_hidden(k1_relat_1(esk7_0),X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.71/0.87  cnf(c_0_63, plain, (r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).
% 0.71/0.87  cnf(c_0_64, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.71/0.87  cnf(c_0_65, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_41]), c_0_58])])).
% 0.71/0.87  cnf(c_0_66, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.71/0.87  cnf(c_0_67, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),k2_relat_1(X1))|~v1_relat_1(X1)|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_51])).
% 0.71/0.87  cnf(c_0_68, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.71/0.87  cnf(c_0_69, negated_conjecture, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,k1_relat_1(esk7_0))),k3_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.71/0.87  cnf(c_0_70, negated_conjecture, (k1_setfam_1(k6_enumset1(k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk7_0)))=k1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.71/0.87  cnf(c_0_71, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(k1_setfam_1(X3),X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_52, c_0_66])).
% 0.71/0.87  cnf(c_0_72, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_41]), c_0_58])])).
% 0.71/0.87  fof(c_0_73, plain, ![X79, X80, X81, X83, X84, X85, X86, X88]:(((~r2_hidden(X81,X80)|r2_hidden(k4_tarski(esk3_3(X79,X80,X81),X81),X79)|X80!=k2_relat_1(X79))&(~r2_hidden(k4_tarski(X84,X83),X79)|r2_hidden(X83,X80)|X80!=k2_relat_1(X79)))&((~r2_hidden(esk4_2(X85,X86),X86)|~r2_hidden(k4_tarski(X88,esk4_2(X85,X86)),X85)|X86=k2_relat_1(X85))&(r2_hidden(esk4_2(X85,X86),X86)|r2_hidden(k4_tarski(esk5_2(X85,X86),esk4_2(X85,X86)),X85)|X86=k2_relat_1(X85)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.71/0.87  cnf(c_0_74, plain, (r1_tarski(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.71/0.87  cnf(c_0_75, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),k3_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.71/0.87  cnf(c_0_76, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(k1_setfam_1(k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X1)),X2)), inference(spm,[status(thm)],[c_0_71, c_0_63])).
% 0.71/0.87  cnf(c_0_77, negated_conjecture, (k1_setfam_1(k6_enumset1(k2_relat_1(esk6_0),k2_relat_1(esk6_0),k2_relat_1(esk6_0),k2_relat_1(esk6_0),k2_relat_1(esk6_0),k2_relat_1(esk6_0),k2_relat_1(esk6_0),k2_relat_1(esk7_0)))=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_64, c_0_72])).
% 0.71/0.87  fof(c_0_78, plain, ![X93, X94, X95]:((r2_hidden(X93,k3_relat_1(X95))|~r2_hidden(k4_tarski(X93,X94),X95)|~v1_relat_1(X95))&(r2_hidden(X94,k3_relat_1(X95))|~r2_hidden(k4_tarski(X93,X94),X95)|~v1_relat_1(X95))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).
% 0.71/0.87  cnf(c_0_79, plain, (r2_hidden(k4_tarski(esk3_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.71/0.87  cnf(c_0_80, negated_conjecture, (r1_tarski(k3_tarski(k6_enumset1(k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),X1)),k3_relat_1(esk7_0))|~r1_tarski(X1,k3_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.71/0.87  cnf(c_0_81, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk7_0),X1),k2_relat_1(esk7_0))|r1_tarski(k2_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.71/0.87  cnf(c_0_82, negated_conjecture, (k3_tarski(k6_enumset1(k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k1_relat_1(esk6_0),k2_relat_1(esk6_0)))=k3_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_40, c_0_51])).
% 0.71/0.87  cnf(c_0_83, negated_conjecture, (~r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.71/0.87  cnf(c_0_84, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.71/0.87  cnf(c_0_85, plain, (r2_hidden(k4_tarski(esk3_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_79])).
% 0.71/0.87  cnf(c_0_86, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk7_0),k3_relat_1(esk7_0)),k2_relat_1(esk7_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_83])).
% 0.71/0.87  cnf(c_0_87, negated_conjecture, (r2_hidden(X1,k3_relat_1(esk7_0))|~r2_hidden(k4_tarski(X2,X1),esk7_0)), inference(spm,[status(thm)],[c_0_84, c_0_41])).
% 0.71/0.87  cnf(c_0_88, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),k3_relat_1(esk7_0))),esk1_2(k2_relat_1(esk7_0),k3_relat_1(esk7_0))),esk7_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.71/0.87  cnf(c_0_89, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.71/0.87  cnf(c_0_90, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk7_0),k3_relat_1(esk7_0)),k3_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.71/0.87  cnf(c_0_91, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),k3_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.71/0.87  cnf(c_0_92, negated_conjecture, (r1_tarski(k1_setfam_1(X1),k3_relat_1(esk7_0))|~r2_hidden(k2_relat_1(esk7_0),X1)), inference(spm,[status(thm)],[c_0_52, c_0_91])).
% 0.71/0.87  cnf(c_0_93, negated_conjecture, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,k2_relat_1(esk7_0))),k3_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_92, c_0_63])).
% 0.71/0.87  cnf(c_0_94, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),k3_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_93, c_0_77])).
% 0.71/0.87  cnf(c_0_95, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_94]), c_0_82]), c_0_83]), ['proof']).
% 0.71/0.87  # SZS output end CNFRefutation
% 0.71/0.87  # Proof object total steps             : 96
% 0.71/0.87  # Proof object clause steps            : 57
% 0.71/0.87  # Proof object formula steps           : 39
% 0.71/0.87  # Proof object conjectures             : 30
% 0.71/0.87  # Proof object clause conjectures      : 27
% 0.71/0.87  # Proof object formula conjectures     : 3
% 0.71/0.87  # Proof object initial clauses used    : 24
% 0.71/0.87  # Proof object initial formulas used   : 19
% 0.71/0.87  # Proof object generating inferences   : 25
% 0.71/0.87  # Proof object simplifying inferences  : 37
% 0.71/0.87  # Training examples: 0 positive, 0 negative
% 0.71/0.87  # Parsed axioms                        : 19
% 0.71/0.87  # Removed by relevancy pruning/SinE    : 0
% 0.71/0.87  # Initial clauses                      : 46
% 0.71/0.87  # Removed in clause preprocessing      : 8
% 0.71/0.87  # Initial clauses in saturation        : 38
% 0.71/0.87  # Processed clauses                    : 1824
% 0.71/0.87  # ...of these trivial                  : 17
% 0.71/0.87  # ...subsumed                          : 760
% 0.71/0.87  # ...remaining for further processing  : 1047
% 0.71/0.87  # Other redundant clauses eliminated   : 379
% 0.71/0.87  # Clauses deleted for lack of memory   : 0
% 0.71/0.87  # Backward-subsumed                    : 75
% 0.71/0.87  # Backward-rewritten                   : 88
% 0.71/0.87  # Generated clauses                    : 28132
% 0.71/0.87  # ...of the previous two non-trivial   : 26977
% 0.71/0.87  # Contextual simplify-reflections      : 8
% 0.71/0.87  # Paramodulations                      : 27465
% 0.71/0.87  # Factorizations                       : 296
% 0.71/0.87  # Equation resolutions                 : 379
% 0.71/0.87  # Propositional unsat checks           : 0
% 0.71/0.87  #    Propositional check models        : 0
% 0.71/0.87  #    Propositional check unsatisfiable : 0
% 0.71/0.87  #    Propositional clauses             : 0
% 0.71/0.87  #    Propositional clauses after purity: 0
% 0.71/0.87  #    Propositional unsat core size     : 0
% 0.71/0.87  #    Propositional preprocessing time  : 0.000
% 0.71/0.87  #    Propositional encoding time       : 0.000
% 0.71/0.87  #    Propositional solver time         : 0.000
% 0.71/0.87  #    Success case prop preproc time    : 0.000
% 0.71/0.87  #    Success case prop encoding time   : 0.000
% 0.71/0.87  #    Success case prop solver time     : 0.000
% 0.71/0.87  # Current number of processed clauses  : 835
% 0.71/0.87  #    Positive orientable unit clauses  : 131
% 0.71/0.87  #    Positive unorientable unit clauses: 0
% 0.71/0.87  #    Negative unit clauses             : 1
% 0.71/0.87  #    Non-unit-clauses                  : 703
% 0.71/0.87  # Current number of unprocessed clauses: 25147
% 0.71/0.87  # ...number of literals in the above   : 111533
% 0.71/0.87  # Current number of archived formulas  : 0
% 0.71/0.87  # Current number of archived clauses   : 209
% 0.71/0.87  # Clause-clause subsumption calls (NU) : 85918
% 0.71/0.87  # Rec. Clause-clause subsumption calls : 35005
% 0.71/0.87  # Non-unit clause-clause subsumptions  : 817
% 0.71/0.87  # Unit Clause-clause subsumption calls : 4274
% 0.71/0.87  # Rewrite failures with RHS unbound    : 0
% 0.71/0.87  # BW rewrite match attempts            : 831
% 0.71/0.87  # BW rewrite match successes           : 10
% 0.71/0.87  # Condensation attempts                : 0
% 0.71/0.87  # Condensation successes               : 0
% 0.71/0.87  # Termbank termtop insertions          : 894565
% 0.71/0.88  
% 0.71/0.88  # -------------------------------------------------
% 0.71/0.88  # User time                : 0.512 s
% 0.71/0.88  # System time              : 0.022 s
% 0.71/0.88  # Total time               : 0.534 s
% 0.71/0.88  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
