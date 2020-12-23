%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:40 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 181 expanded)
%              Number of clauses        :   41 (  76 expanded)
%              Number of leaves         :   15 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  208 ( 554 expanded)
%              Number of equality atoms :   85 ( 271 expanded)
%              Maximal formula depth    :   47 (   4 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

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

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(c_0_15,plain,(
    ! [X64,X65] : k1_setfam_1(k2_tarski(X64,X65)) = k3_xboole_0(X64,X65) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_16,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X11,X12] : r1_tarski(k3_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_21,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_22,plain,(
    ! [X25,X26,X27,X28,X29] : k4_enumset1(X25,X25,X26,X27,X28,X29) = k3_enumset1(X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_23,plain,(
    ! [X30,X31,X32,X33,X34,X35] : k5_enumset1(X30,X30,X31,X32,X33,X34,X35) = k4_enumset1(X30,X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_24,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42] : k6_enumset1(X36,X36,X37,X38,X39,X40,X41,X42) = k5_enumset1(X36,X37,X38,X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_25,plain,(
    ! [X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58,X59,X60,X61,X62] :
      ( ( ~ r2_hidden(X52,X51)
        | X52 = X43
        | X52 = X44
        | X52 = X45
        | X52 = X46
        | X52 = X47
        | X52 = X48
        | X52 = X49
        | X52 = X50
        | X51 != k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) )
      & ( X53 != X43
        | r2_hidden(X53,X51)
        | X51 != k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) )
      & ( X53 != X44
        | r2_hidden(X53,X51)
        | X51 != k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) )
      & ( X53 != X45
        | r2_hidden(X53,X51)
        | X51 != k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) )
      & ( X53 != X46
        | r2_hidden(X53,X51)
        | X51 != k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) )
      & ( X53 != X47
        | r2_hidden(X53,X51)
        | X51 != k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) )
      & ( X53 != X48
        | r2_hidden(X53,X51)
        | X51 != k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) )
      & ( X53 != X49
        | r2_hidden(X53,X51)
        | X51 != k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) )
      & ( X53 != X50
        | r2_hidden(X53,X51)
        | X51 != k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) )
      & ( esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) != X54
        | ~ r2_hidden(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) != X55
        | ~ r2_hidden(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) != X56
        | ~ r2_hidden(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) != X57
        | ~ r2_hidden(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) != X58
        | ~ r2_hidden(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) != X59
        | ~ r2_hidden(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) != X60
        | ~ r2_hidden(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) != X61
        | ~ r2_hidden(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( r2_hidden(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)
        | esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) = X54
        | esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) = X55
        | esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) = X56
        | esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) = X57
        | esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) = X58
        | esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) = X59
        | esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) = X60
        | esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) = X61
        | X62 = k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

fof(c_0_27,plain,(
    ! [X66,X67] :
      ( ( ~ m1_subset_1(X66,k1_zfmisc_1(X67))
        | r1_tarski(X66,X67) )
      & ( ~ r1_tarski(X66,X67)
        | m1_subset_1(X66,k1_zfmisc_1(X67)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_28,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_35,plain,(
    ! [X68,X69] :
      ( ~ r2_hidden(X68,X69)
      | r1_tarski(k1_setfam_1(X69),X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_37,plain,(
    ! [X72,X73,X74] :
      ( ~ v1_relat_1(X72)
      | ~ v1_relat_1(X73)
      | ~ v1_relat_1(X74)
      | ~ r1_tarski(X72,X73)
      | r1_tarski(k5_relat_1(X74,X72),k5_relat_1(X74,X73)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).

fof(c_0_38,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & ~ r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_39,plain,(
    ! [X70,X71] :
      ( ~ v1_relat_1(X70)
      | ~ m1_subset_1(X71,k1_zfmisc_1(X70))
      | v1_relat_1(X71) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_36])])).

cnf(c_0_44,plain,
    ( r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X2,X5,X6,X7,X8,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)),X8) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_50,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X13,X15)
      | r1_tarski(X13,k3_xboole_0(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk3_0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( v1_relat_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X1,X3,X4,X5,X6,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_56,plain,
    ( m1_subset_1(k1_setfam_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)),k1_zfmisc_1(X8)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_49])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk3_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( v1_relat_1(k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_45])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk4_0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X2,esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_55])).

cnf(c_0_62,plain,
    ( v1_relat_1(k1_setfam_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)))
    | ~ v1_relat_1(X8) ),
    inference(spm,[status(thm)],[c_0_46,c_0_56])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),k5_relat_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk4_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_52])).

cnf(c_0_66,negated_conjecture,
    ( v1_relat_1(k1_setfam_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_55])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),X2)))
    | ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,esk4_0))),k5_relat_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_49])])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:02:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.49  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002I
% 0.20/0.49  # and selection function SelectNegativeLiterals.
% 0.20/0.49  #
% 0.20/0.49  # Preprocessing time       : 0.028 s
% 0.20/0.49  # Presaturation interreduction done
% 0.20/0.49  
% 0.20/0.49  # Proof found!
% 0.20/0.49  # SZS status Theorem
% 0.20/0.49  # SZS output start CNFRefutation
% 0.20/0.49  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.49  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.49  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.49  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.49  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.49  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.49  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.49  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.49  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 0.20/0.49  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 0.20/0.49  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.49  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.20/0.49  fof(t48_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 0.20/0.49  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.49  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.20/0.49  fof(c_0_15, plain, ![X64, X65]:k1_setfam_1(k2_tarski(X64,X65))=k3_xboole_0(X64,X65), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.49  fof(c_0_16, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.49  fof(c_0_17, plain, ![X11, X12]:r1_tarski(k3_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.49  cnf(c_0_18, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.49  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.49  fof(c_0_20, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.49  fof(c_0_21, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.49  fof(c_0_22, plain, ![X25, X26, X27, X28, X29]:k4_enumset1(X25,X25,X26,X27,X28,X29)=k3_enumset1(X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.49  fof(c_0_23, plain, ![X30, X31, X32, X33, X34, X35]:k5_enumset1(X30,X30,X31,X32,X33,X34,X35)=k4_enumset1(X30,X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.49  fof(c_0_24, plain, ![X36, X37, X38, X39, X40, X41, X42]:k6_enumset1(X36,X36,X37,X38,X39,X40,X41,X42)=k5_enumset1(X36,X37,X38,X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.49  fof(c_0_25, plain, ![X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59, X60, X61, X62]:(((~r2_hidden(X52,X51)|(X52=X43|X52=X44|X52=X45|X52=X46|X52=X47|X52=X48|X52=X49|X52=X50)|X51!=k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50))&((((((((X53!=X43|r2_hidden(X53,X51)|X51!=k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50))&(X53!=X44|r2_hidden(X53,X51)|X51!=k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50)))&(X53!=X45|r2_hidden(X53,X51)|X51!=k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50)))&(X53!=X46|r2_hidden(X53,X51)|X51!=k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50)))&(X53!=X47|r2_hidden(X53,X51)|X51!=k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50)))&(X53!=X48|r2_hidden(X53,X51)|X51!=k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50)))&(X53!=X49|r2_hidden(X53,X51)|X51!=k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50)))&(X53!=X50|r2_hidden(X53,X51)|X51!=k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50))))&(((((((((esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)!=X54|~r2_hidden(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)|X62=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61))&(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)!=X55|~r2_hidden(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)|X62=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)!=X56|~r2_hidden(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)|X62=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)!=X57|~r2_hidden(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)|X62=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)!=X58|~r2_hidden(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)|X62=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)!=X59|~r2_hidden(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)|X62=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)!=X60|~r2_hidden(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)|X62=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)!=X61|~r2_hidden(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)|X62=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(r2_hidden(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)|(esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)=X54|esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)=X55|esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)=X56|esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)=X57|esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)=X58|esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)=X59|esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)=X60|esk1_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)=X61)|X62=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.20/0.49  fof(c_0_26, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 0.20/0.49  fof(c_0_27, plain, ![X66, X67]:((~m1_subset_1(X66,k1_zfmisc_1(X67))|r1_tarski(X66,X67))&(~r1_tarski(X66,X67)|m1_subset_1(X66,k1_zfmisc_1(X67)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.49  cnf(c_0_28, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.49  cnf(c_0_29, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.49  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.49  cnf(c_0_31, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.49  cnf(c_0_32, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.49  cnf(c_0_33, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.49  cnf(c_0_34, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.49  fof(c_0_35, plain, ![X68, X69]:(~r2_hidden(X68,X69)|r1_tarski(k1_setfam_1(X69),X68)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.20/0.49  cnf(c_0_36, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.49  fof(c_0_37, plain, ![X72, X73, X74]:(~v1_relat_1(X72)|(~v1_relat_1(X73)|(~v1_relat_1(X74)|(~r1_tarski(X72,X73)|r1_tarski(k5_relat_1(X74,X72),k5_relat_1(X74,X73)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).
% 0.20/0.49  fof(c_0_38, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&~r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.20/0.49  fof(c_0_39, plain, ![X70, X71]:(~v1_relat_1(X70)|(~m1_subset_1(X71,k1_zfmisc_1(X70))|v1_relat_1(X71))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.49  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.49  cnf(c_0_41, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])).
% 0.20/0.49  cnf(c_0_42, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.49  cnf(c_0_43, plain, (r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_36])])).
% 0.20/0.49  cnf(c_0_44, plain, (r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.49  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.49  cnf(c_0_46, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.49  cnf(c_0_47, plain, (m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.49  cnf(c_0_48, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X2,X5,X6,X7,X8,X9,X10)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.49  cnf(c_0_49, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)),X8)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.49  fof(c_0_50, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X13,X15)|r1_tarski(X13,k3_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.20/0.49  cnf(c_0_51, negated_conjecture, (r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk3_0))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X2,esk3_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.49  cnf(c_0_52, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.49  cnf(c_0_53, plain, (v1_relat_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.49  cnf(c_0_54, plain, (r2_hidden(X1,k6_enumset1(X2,X1,X3,X4,X5,X6,X7,X8))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).
% 0.20/0.49  cnf(c_0_55, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.49  cnf(c_0_56, plain, (m1_subset_1(k1_setfam_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)),k1_zfmisc_1(X8))), inference(spm,[status(thm)],[c_0_40, c_0_49])).
% 0.20/0.49  cnf(c_0_57, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.49  cnf(c_0_58, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk3_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.49  cnf(c_0_59, negated_conjecture, (v1_relat_1(k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)))), inference(spm,[status(thm)],[c_0_53, c_0_45])).
% 0.20/0.49  cnf(c_0_60, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)),X2)), inference(spm,[status(thm)],[c_0_42, c_0_54])).
% 0.20/0.49  cnf(c_0_61, negated_conjecture, (r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk4_0))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X2,esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_55])).
% 0.20/0.49  cnf(c_0_62, plain, (v1_relat_1(k1_setfam_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)))|~v1_relat_1(X8)), inference(spm,[status(thm)],[c_0_46, c_0_56])).
% 0.20/0.49  cnf(c_0_63, plain, (r1_tarski(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])).
% 0.20/0.49  cnf(c_0_64, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),k5_relat_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])])).
% 0.20/0.49  cnf(c_0_65, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk4_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_61, c_0_52])).
% 0.20/0.49  cnf(c_0_66, negated_conjecture, (v1_relat_1(k1_setfam_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,esk4_0)))), inference(spm,[status(thm)],[c_0_62, c_0_55])).
% 0.20/0.49  cnf(c_0_67, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.49  cnf(c_0_68, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),X2)))|~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),X2)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.49  cnf(c_0_69, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,esk4_0))),k5_relat_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_49])])).
% 0.20/0.49  cnf(c_0_70, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k6_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34])).
% 0.20/0.49  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), ['proof']).
% 0.20/0.49  # SZS output end CNFRefutation
% 0.20/0.49  # Proof object total steps             : 72
% 0.20/0.49  # Proof object clause steps            : 41
% 0.20/0.49  # Proof object formula steps           : 31
% 0.20/0.49  # Proof object conjectures             : 18
% 0.20/0.49  # Proof object clause conjectures      : 15
% 0.20/0.49  # Proof object formula conjectures     : 3
% 0.20/0.49  # Proof object initial clauses used    : 19
% 0.20/0.49  # Proof object initial formulas used   : 15
% 0.20/0.49  # Proof object generating inferences   : 16
% 0.20/0.49  # Proof object simplifying inferences  : 34
% 0.20/0.49  # Training examples: 0 positive, 0 negative
% 0.20/0.49  # Parsed axioms                        : 15
% 0.20/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.49  # Initial clauses                      : 36
% 0.20/0.49  # Removed in clause preprocessing      : 7
% 0.20/0.49  # Initial clauses in saturation        : 29
% 0.20/0.49  # Processed clauses                    : 354
% 0.20/0.49  # ...of these trivial                  : 7
% 0.20/0.49  # ...subsumed                          : 81
% 0.20/0.49  # ...remaining for further processing  : 266
% 0.20/0.49  # Other redundant clauses eliminated   : 377
% 0.20/0.49  # Clauses deleted for lack of memory   : 0
% 0.20/0.49  # Backward-subsumed                    : 4
% 0.20/0.49  # Backward-rewritten                   : 5
% 0.20/0.49  # Generated clauses                    : 3281
% 0.20/0.49  # ...of the previous two non-trivial   : 2870
% 0.20/0.49  # Contextual simplify-reflections      : 0
% 0.20/0.49  # Paramodulations                      : 2672
% 0.20/0.49  # Factorizations                       : 240
% 0.20/0.49  # Equation resolutions                 : 377
% 0.20/0.49  # Propositional unsat checks           : 0
% 0.20/0.49  #    Propositional check models        : 0
% 0.20/0.49  #    Propositional check unsatisfiable : 0
% 0.20/0.49  #    Propositional clauses             : 0
% 0.20/0.49  #    Propositional clauses after purity: 0
% 0.20/0.49  #    Propositional unsat core size     : 0
% 0.20/0.49  #    Propositional preprocessing time  : 0.000
% 0.20/0.49  #    Propositional encoding time       : 0.000
% 0.20/0.49  #    Propositional solver time         : 0.000
% 0.20/0.49  #    Success case prop preproc time    : 0.000
% 0.20/0.49  #    Success case prop encoding time   : 0.000
% 0.20/0.49  #    Success case prop solver time     : 0.000
% 0.20/0.49  # Current number of processed clauses  : 219
% 0.20/0.49  #    Positive orientable unit clauses  : 81
% 0.20/0.49  #    Positive unorientable unit clauses: 0
% 0.20/0.49  #    Negative unit clauses             : 1
% 0.20/0.49  #    Non-unit-clauses                  : 137
% 0.20/0.49  # Current number of unprocessed clauses: 2450
% 0.20/0.49  # ...number of literals in the above   : 9821
% 0.20/0.49  # Current number of archived formulas  : 0
% 0.20/0.49  # Current number of archived clauses   : 45
% 0.20/0.49  # Clause-clause subsumption calls (NU) : 1933
% 0.20/0.49  # Rec. Clause-clause subsumption calls : 1824
% 0.20/0.49  # Non-unit clause-clause subsumptions  : 85
% 0.20/0.49  # Unit Clause-clause subsumption calls : 536
% 0.20/0.49  # Rewrite failures with RHS unbound    : 0
% 0.20/0.49  # BW rewrite match attempts            : 478
% 0.20/0.49  # BW rewrite match successes           : 5
% 0.20/0.49  # Condensation attempts                : 0
% 0.20/0.49  # Condensation successes               : 0
% 0.20/0.49  # Termbank termtop insertions          : 76239
% 0.20/0.49  
% 0.20/0.49  # -------------------------------------------------
% 0.20/0.49  # User time                : 0.145 s
% 0.20/0.49  # System time              : 0.008 s
% 0.20/0.49  # Total time               : 0.152 s
% 0.20/0.49  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
