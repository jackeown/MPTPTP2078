%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:39 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 266 expanded)
%              Number of clauses        :   31 (  95 expanded)
%              Number of leaves         :   15 (  83 expanded)
%              Depth                    :    9
%              Number of atoms          :  163 ( 415 expanded)
%              Number of equality atoms :  110 ( 314 expanded)
%              Maximal formula depth    :   32 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(t65_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,k1_tarski(X2))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ( r2_hidden(X3,X1)
       => k1_funct_1(X4,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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

fof(t11_setfam_1,axiom,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

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

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(c_0_15,plain,(
    ! [X57,X58] : k1_setfam_1(k2_tarski(X57,X58)) = k3_xboole_0(X57,X58) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_16,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

fof(c_0_21,plain,(
    ! [X39,X40] :
      ( ( k4_xboole_0(k1_tarski(X39),k1_tarski(X40)) != k1_tarski(X39)
        | X39 != X40 )
      & ( X39 = X40
        | k4_xboole_0(k1_tarski(X39),k1_tarski(X40)) = k1_tarski(X39) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_22,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_25,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X17,X18,X19,X20] : k3_enumset1(X17,X17,X18,X19,X20) = k2_enumset1(X17,X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X21,X22,X23,X24,X25] : k4_enumset1(X21,X21,X22,X23,X24,X25) = k3_enumset1(X21,X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_28,plain,(
    ! [X26,X27,X28,X29,X30,X31] : k5_enumset1(X26,X26,X27,X28,X29,X30,X31) = k4_enumset1(X26,X27,X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_29,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38] : k6_enumset1(X32,X32,X33,X34,X35,X36,X37,X38) = k5_enumset1(X32,X33,X34,X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_30,plain,(
    ! [X56] : k1_setfam_1(k1_tarski(X56)) = X56 ),
    inference(variable_rename,[status(thm)],[t11_setfam_1])).

fof(c_0_31,plain,(
    ! [X41,X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54] :
      ( ( ~ r2_hidden(X47,X46)
        | X47 = X41
        | X47 = X42
        | X47 = X43
        | X47 = X44
        | X47 = X45
        | X46 != k3_enumset1(X41,X42,X43,X44,X45) )
      & ( X48 != X41
        | r2_hidden(X48,X46)
        | X46 != k3_enumset1(X41,X42,X43,X44,X45) )
      & ( X48 != X42
        | r2_hidden(X48,X46)
        | X46 != k3_enumset1(X41,X42,X43,X44,X45) )
      & ( X48 != X43
        | r2_hidden(X48,X46)
        | X46 != k3_enumset1(X41,X42,X43,X44,X45) )
      & ( X48 != X44
        | r2_hidden(X48,X46)
        | X46 != k3_enumset1(X41,X42,X43,X44,X45) )
      & ( X48 != X45
        | r2_hidden(X48,X46)
        | X46 != k3_enumset1(X41,X42,X43,X44,X45) )
      & ( esk1_6(X49,X50,X51,X52,X53,X54) != X49
        | ~ r2_hidden(esk1_6(X49,X50,X51,X52,X53,X54),X54)
        | X54 = k3_enumset1(X49,X50,X51,X52,X53) )
      & ( esk1_6(X49,X50,X51,X52,X53,X54) != X50
        | ~ r2_hidden(esk1_6(X49,X50,X51,X52,X53,X54),X54)
        | X54 = k3_enumset1(X49,X50,X51,X52,X53) )
      & ( esk1_6(X49,X50,X51,X52,X53,X54) != X51
        | ~ r2_hidden(esk1_6(X49,X50,X51,X52,X53,X54),X54)
        | X54 = k3_enumset1(X49,X50,X51,X52,X53) )
      & ( esk1_6(X49,X50,X51,X52,X53,X54) != X52
        | ~ r2_hidden(esk1_6(X49,X50,X51,X52,X53,X54),X54)
        | X54 = k3_enumset1(X49,X50,X51,X52,X53) )
      & ( esk1_6(X49,X50,X51,X52,X53,X54) != X53
        | ~ r2_hidden(esk1_6(X49,X50,X51,X52,X53,X54),X54)
        | X54 = k3_enumset1(X49,X50,X51,X52,X53) )
      & ( r2_hidden(esk1_6(X49,X50,X51,X52,X53,X54),X54)
        | esk1_6(X49,X50,X51,X52,X53,X54) = X49
        | esk1_6(X49,X50,X51,X52,X53,X54) = X50
        | esk1_6(X49,X50,X51,X52,X53,X54) = X51
        | esk1_6(X49,X50,X51,X52,X53,X54) = X52
        | esk1_6(X49,X50,X51,X52,X53,X54) = X53
        | X54 = k3_enumset1(X49,X50,X51,X52,X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).

fof(c_0_32,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0))))
    & r2_hidden(esk4_0,esk2_0)
    & k1_funct_1(esk5_0,esk4_0) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_42,plain,(
    ! [X10] : k5_xboole_0(X10,X10) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_43,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | ~ r2_hidden(X1,X2)
    | X2 != k3_enumset1(X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_44,plain,(
    ! [X59,X60,X61,X62] :
      ( ~ v1_funct_1(X62)
      | ~ v1_funct_2(X62,X59,X60)
      | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
      | ~ r2_hidden(X61,X59)
      | X60 = k1_xboole_0
      | r2_hidden(k1_funct_1(X62,X61),X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( X1 != X2
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34]),c_0_34]),c_0_19]),c_0_19]),c_0_19]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_34]),c_0_19]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( X1 = X7
    | X1 = X6
    | X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_51,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_34]),c_0_19]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_34]),c_0_19]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_55,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_56,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | ~ r2_hidden(X1,k6_enumset1(X6,X6,X6,X6,X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,X1),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])]),c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(esk5_0,esk4_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_59,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = esk3_0
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.09  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.08/0.28  % Computer   : n016.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % WCLimit    : 600
% 0.08/0.28  % DateTime   : Tue Dec  1 20:47:49 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.08/0.28  # Version: 2.5pre002
% 0.08/0.28  # No SInE strategy applied
% 0.08/0.28  # Trying AutoSched0 for 299 seconds
% 0.08/0.30  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.08/0.30  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.08/0.30  #
% 0.08/0.30  # Preprocessing time       : 0.017 s
% 0.08/0.30  # Presaturation interreduction done
% 0.08/0.30  
% 0.08/0.30  # Proof found!
% 0.08/0.30  # SZS status Theorem
% 0.08/0.30  # SZS output start CNFRefutation
% 0.08/0.30  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.08/0.30  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.08/0.30  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.08/0.30  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 0.08/0.30  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.08/0.30  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.08/0.30  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.08/0.30  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.08/0.30  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.08/0.30  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.08/0.30  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.08/0.30  fof(t11_setfam_1, axiom, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.08/0.30  fof(d3_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:(X6=k3_enumset1(X1,X2,X3,X4,X5)<=>![X7]:(r2_hidden(X7,X6)<=>~(((((X7!=X1&X7!=X2)&X7!=X3)&X7!=X4)&X7!=X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 0.08/0.30  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.08/0.30  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 0.08/0.30  fof(c_0_15, plain, ![X57, X58]:k1_setfam_1(k2_tarski(X57,X58))=k3_xboole_0(X57,X58), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.08/0.30  fof(c_0_16, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.08/0.30  fof(c_0_17, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.08/0.30  cnf(c_0_18, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.08/0.30  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.08/0.30  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.08/0.30  fof(c_0_21, plain, ![X39, X40]:((k4_xboole_0(k1_tarski(X39),k1_tarski(X40))!=k1_tarski(X39)|X39!=X40)&(X39=X40|k4_xboole_0(k1_tarski(X39),k1_tarski(X40))=k1_tarski(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.08/0.30  fof(c_0_22, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.08/0.30  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.08/0.30  cnf(c_0_24, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.08/0.30  fof(c_0_25, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.08/0.30  fof(c_0_26, plain, ![X17, X18, X19, X20]:k3_enumset1(X17,X17,X18,X19,X20)=k2_enumset1(X17,X18,X19,X20), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.08/0.30  fof(c_0_27, plain, ![X21, X22, X23, X24, X25]:k4_enumset1(X21,X21,X22,X23,X24,X25)=k3_enumset1(X21,X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.08/0.30  fof(c_0_28, plain, ![X26, X27, X28, X29, X30, X31]:k5_enumset1(X26,X26,X27,X28,X29,X30,X31)=k4_enumset1(X26,X27,X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.08/0.30  fof(c_0_29, plain, ![X32, X33, X34, X35, X36, X37, X38]:k6_enumset1(X32,X32,X33,X34,X35,X36,X37,X38)=k5_enumset1(X32,X33,X34,X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.08/0.30  fof(c_0_30, plain, ![X56]:k1_setfam_1(k1_tarski(X56))=X56, inference(variable_rename,[status(thm)],[t11_setfam_1])).
% 0.08/0.30  fof(c_0_31, plain, ![X41, X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54]:(((~r2_hidden(X47,X46)|(X47=X41|X47=X42|X47=X43|X47=X44|X47=X45)|X46!=k3_enumset1(X41,X42,X43,X44,X45))&(((((X48!=X41|r2_hidden(X48,X46)|X46!=k3_enumset1(X41,X42,X43,X44,X45))&(X48!=X42|r2_hidden(X48,X46)|X46!=k3_enumset1(X41,X42,X43,X44,X45)))&(X48!=X43|r2_hidden(X48,X46)|X46!=k3_enumset1(X41,X42,X43,X44,X45)))&(X48!=X44|r2_hidden(X48,X46)|X46!=k3_enumset1(X41,X42,X43,X44,X45)))&(X48!=X45|r2_hidden(X48,X46)|X46!=k3_enumset1(X41,X42,X43,X44,X45))))&((((((esk1_6(X49,X50,X51,X52,X53,X54)!=X49|~r2_hidden(esk1_6(X49,X50,X51,X52,X53,X54),X54)|X54=k3_enumset1(X49,X50,X51,X52,X53))&(esk1_6(X49,X50,X51,X52,X53,X54)!=X50|~r2_hidden(esk1_6(X49,X50,X51,X52,X53,X54),X54)|X54=k3_enumset1(X49,X50,X51,X52,X53)))&(esk1_6(X49,X50,X51,X52,X53,X54)!=X51|~r2_hidden(esk1_6(X49,X50,X51,X52,X53,X54),X54)|X54=k3_enumset1(X49,X50,X51,X52,X53)))&(esk1_6(X49,X50,X51,X52,X53,X54)!=X52|~r2_hidden(esk1_6(X49,X50,X51,X52,X53,X54),X54)|X54=k3_enumset1(X49,X50,X51,X52,X53)))&(esk1_6(X49,X50,X51,X52,X53,X54)!=X53|~r2_hidden(esk1_6(X49,X50,X51,X52,X53,X54),X54)|X54=k3_enumset1(X49,X50,X51,X52,X53)))&(r2_hidden(esk1_6(X49,X50,X51,X52,X53,X54),X54)|(esk1_6(X49,X50,X51,X52,X53,X54)=X49|esk1_6(X49,X50,X51,X52,X53,X54)=X50|esk1_6(X49,X50,X51,X52,X53,X54)=X51|esk1_6(X49,X50,X51,X52,X53,X54)=X52|esk1_6(X49,X50,X51,X52,X53,X54)=X53)|X54=k3_enumset1(X49,X50,X51,X52,X53)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).
% 0.08/0.30  fof(c_0_32, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))))&(r2_hidden(esk4_0,esk2_0)&k1_funct_1(esk5_0,esk4_0)!=esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.08/0.30  cnf(c_0_33, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.08/0.30  cnf(c_0_34, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.08/0.30  cnf(c_0_35, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.08/0.30  cnf(c_0_36, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.08/0.30  cnf(c_0_37, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.08/0.30  cnf(c_0_38, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.08/0.30  cnf(c_0_39, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.08/0.30  cnf(c_0_40, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.08/0.30  cnf(c_0_41, plain, (k1_setfam_1(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.08/0.30  fof(c_0_42, plain, ![X10]:k5_xboole_0(X10,X10)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.08/0.30  cnf(c_0_43, plain, (X1=X3|X1=X4|X1=X5|X1=X6|X1=X7|~r2_hidden(X1,X2)|X2!=k3_enumset1(X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.08/0.30  fof(c_0_44, plain, ![X59, X60, X61, X62]:(~v1_funct_1(X62)|~v1_funct_2(X62,X59,X60)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))|(~r2_hidden(X61,X59)|(X60=k1_xboole_0|r2_hidden(k1_funct_1(X62,X61),X60)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.08/0.30  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.08/0.30  cnf(c_0_46, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.08/0.30  cnf(c_0_47, plain, (X1!=X2|k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_34]), c_0_34]), c_0_19]), c_0_19]), c_0_19]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 0.08/0.30  cnf(c_0_48, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_34]), c_0_19]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.08/0.30  cnf(c_0_49, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.08/0.30  cnf(c_0_50, plain, (X1=X7|X1=X6|X1=X5|X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_38]), c_0_39]), c_0_40])).
% 0.08/0.30  cnf(c_0_51, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.08/0.30  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_34]), c_0_19]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.08/0.30  cnf(c_0_53, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_34]), c_0_19]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.08/0.30  cnf(c_0_54, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.08/0.30  cnf(c_0_55, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_47]), c_0_48]), c_0_49])).
% 0.08/0.30  cnf(c_0_56, plain, (X1=X2|X1=X3|X1=X4|X1=X5|X1=X6|~r2_hidden(X1,k6_enumset1(X6,X6,X6,X6,X5,X4,X3,X2))), inference(er,[status(thm)],[c_0_50])).
% 0.08/0.30  cnf(c_0_57, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,X1),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|~r2_hidden(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54])]), c_0_55])).
% 0.08/0.30  cnf(c_0_58, negated_conjecture, (k1_funct_1(esk5_0,esk4_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.08/0.30  cnf(c_0_59, negated_conjecture, (k1_funct_1(esk5_0,X1)=esk3_0|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.08/0.30  cnf(c_0_60, negated_conjecture, (r2_hidden(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.08/0.30  cnf(c_0_61, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])]), ['proof']).
% 0.08/0.30  # SZS output end CNFRefutation
% 0.08/0.30  # Proof object total steps             : 62
% 0.08/0.30  # Proof object clause steps            : 31
% 0.08/0.30  # Proof object formula steps           : 31
% 0.08/0.30  # Proof object conjectures             : 13
% 0.08/0.30  # Proof object clause conjectures      : 10
% 0.08/0.30  # Proof object formula conjectures     : 3
% 0.08/0.30  # Proof object initial clauses used    : 19
% 0.08/0.30  # Proof object initial formulas used   : 15
% 0.08/0.30  # Proof object generating inferences   : 3
% 0.08/0.30  # Proof object simplifying inferences  : 83
% 0.08/0.30  # Training examples: 0 positive, 0 negative
% 0.08/0.30  # Parsed axioms                        : 15
% 0.08/0.30  # Removed by relevancy pruning/SinE    : 0
% 0.08/0.30  # Initial clauses                      : 31
% 0.08/0.30  # Removed in clause preprocessing      : 9
% 0.08/0.30  # Initial clauses in saturation        : 22
% 0.08/0.30  # Processed clauses                    : 46
% 0.08/0.30  # ...of these trivial                  : 0
% 0.08/0.30  # ...subsumed                          : 0
% 0.08/0.30  # ...remaining for further processing  : 46
% 0.08/0.30  # Other redundant clauses eliminated   : 12
% 0.08/0.30  # Clauses deleted for lack of memory   : 0
% 0.08/0.30  # Backward-subsumed                    : 0
% 0.08/0.30  # Backward-rewritten                   : 0
% 0.08/0.30  # Generated clauses                    : 11
% 0.08/0.30  # ...of the previous two non-trivial   : 9
% 0.08/0.30  # Contextual simplify-reflections      : 0
% 0.08/0.30  # Paramodulations                      : 4
% 0.08/0.30  # Factorizations                       : 0
% 0.08/0.30  # Equation resolutions                 : 12
% 0.08/0.30  # Propositional unsat checks           : 0
% 0.08/0.30  #    Propositional check models        : 0
% 0.08/0.30  #    Propositional check unsatisfiable : 0
% 0.08/0.30  #    Propositional clauses             : 0
% 0.08/0.30  #    Propositional clauses after purity: 0
% 0.08/0.30  #    Propositional unsat core size     : 0
% 0.08/0.30  #    Propositional preprocessing time  : 0.000
% 0.08/0.30  #    Propositional encoding time       : 0.000
% 0.08/0.30  #    Propositional solver time         : 0.000
% 0.08/0.30  #    Success case prop preproc time    : 0.000
% 0.08/0.30  #    Success case prop encoding time   : 0.000
% 0.08/0.30  #    Success case prop solver time     : 0.000
% 0.08/0.30  # Current number of processed clauses  : 17
% 0.08/0.30  #    Positive orientable unit clauses  : 11
% 0.08/0.30  #    Positive unorientable unit clauses: 0
% 0.08/0.30  #    Negative unit clauses             : 2
% 0.08/0.30  #    Non-unit-clauses                  : 4
% 0.08/0.30  # Current number of unprocessed clauses: 7
% 0.08/0.30  # ...number of literals in the above   : 24
% 0.08/0.30  # Current number of archived formulas  : 0
% 0.08/0.30  # Current number of archived clauses   : 31
% 0.08/0.30  # Clause-clause subsumption calls (NU) : 21
% 0.08/0.30  # Rec. Clause-clause subsumption calls : 21
% 0.08/0.30  # Non-unit clause-clause subsumptions  : 0
% 0.08/0.30  # Unit Clause-clause subsumption calls : 0
% 0.08/0.30  # Rewrite failures with RHS unbound    : 0
% 0.08/0.30  # BW rewrite match attempts            : 20
% 0.08/0.30  # BW rewrite match successes           : 0
% 0.08/0.30  # Condensation attempts                : 0
% 0.08/0.30  # Condensation successes               : 0
% 0.08/0.30  # Termbank termtop insertions          : 2076
% 0.08/0.30  
% 0.08/0.30  # -------------------------------------------------
% 0.08/0.30  # User time                : 0.014 s
% 0.08/0.30  # System time              : 0.007 s
% 0.08/0.30  # Total time               : 0.020 s
% 0.08/0.30  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
