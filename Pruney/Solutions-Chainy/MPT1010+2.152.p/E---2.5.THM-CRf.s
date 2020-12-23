%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:32 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 168 expanded)
%              Number of clauses        :   32 (  66 expanded)
%              Number of leaves         :   13 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  203 ( 389 expanded)
%              Number of equality atoms :  127 ( 245 expanded)
%              Maximal formula depth    :   47 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,k1_tarski(X2))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ( r2_hidden(X3,X1)
       => k1_funct_1(X4,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(t12_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
     => ( k1_mcart_1(X1) = X2
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

fof(c_0_14,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))
    & r2_hidden(esk5_0,esk3_0)
    & k1_funct_1(esk6_0,esk5_0) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_15,plain,(
    ! [X18] : k2_tarski(X18,X18) = k1_tarski(X18) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X24,X25,X26,X27] : k3_enumset1(X24,X24,X25,X26,X27) = k2_enumset1(X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_19,plain,(
    ! [X28,X29,X30,X31,X32] : k4_enumset1(X28,X28,X29,X30,X31,X32) = k3_enumset1(X28,X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_20,plain,(
    ! [X33,X34,X35,X36,X37,X38] : k5_enumset1(X33,X33,X34,X35,X36,X37,X38) = k4_enumset1(X33,X34,X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_21,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45] : k6_enumset1(X39,X39,X40,X41,X42,X43,X44,X45) = k5_enumset1(X39,X40,X41,X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_22,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X13,X12)
        | X13 = X11
        | X12 != k1_tarski(X11) )
      & ( X14 != X11
        | r2_hidden(X14,X12)
        | X12 != k1_tarski(X11) )
      & ( ~ r2_hidden(esk1_2(X15,X16),X16)
        | esk1_2(X15,X16) != X15
        | X16 = k1_tarski(X15) )
      & ( r2_hidden(esk1_2(X15,X16),X16)
        | esk1_2(X15,X16) = X15
        | X16 = k1_tarski(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_23,plain,(
    ! [X72,X73,X74,X75] :
      ( ~ v1_funct_1(X75)
      | ~ v1_funct_2(X75,X72,X73)
      | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X72,X73)))
      | ~ r2_hidden(X74,X72)
      | X73 = k1_xboole_0
      | r2_hidden(k1_funct_1(X75,X74),X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_33,plain,(
    ! [X69,X70,X71] :
      ( ( k1_mcart_1(X69) = X70
        | ~ r2_hidden(X69,k2_zfmisc_1(k1_tarski(X70),X71)) )
      & ( r2_hidden(k2_mcart_1(X69),X71)
        | ~ r2_hidden(X69,k2_zfmisc_1(k1_tarski(X70),X71)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).

fof(c_0_34,plain,(
    ! [X46,X47] :
      ( ( k2_zfmisc_1(X46,X47) != k1_xboole_0
        | X46 = k1_xboole_0
        | X47 = k1_xboole_0 )
      & ( X46 != k1_xboole_0
        | k2_zfmisc_1(X46,X47) = k1_xboole_0 )
      & ( X47 != k1_xboole_0
        | k2_zfmisc_1(X46,X47) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_35,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58,X59,X60,X61,X62,X63,X64,X65,X66,X67] :
      ( ( ~ r2_hidden(X57,X56)
        | X57 = X48
        | X57 = X49
        | X57 = X50
        | X57 = X51
        | X57 = X52
        | X57 = X53
        | X57 = X54
        | X57 = X55
        | X56 != k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55) )
      & ( X58 != X48
        | r2_hidden(X58,X56)
        | X56 != k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55) )
      & ( X58 != X49
        | r2_hidden(X58,X56)
        | X56 != k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55) )
      & ( X58 != X50
        | r2_hidden(X58,X56)
        | X56 != k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55) )
      & ( X58 != X51
        | r2_hidden(X58,X56)
        | X56 != k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55) )
      & ( X58 != X52
        | r2_hidden(X58,X56)
        | X56 != k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55) )
      & ( X58 != X53
        | r2_hidden(X58,X56)
        | X56 != k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55) )
      & ( X58 != X54
        | r2_hidden(X58,X56)
        | X56 != k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55) )
      & ( X58 != X55
        | r2_hidden(X58,X56)
        | X56 != k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55) )
      & ( esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67) != X59
        | ~ r2_hidden(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67),X67)
        | X67 = k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66) )
      & ( esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67) != X60
        | ~ r2_hidden(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67),X67)
        | X67 = k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66) )
      & ( esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67) != X61
        | ~ r2_hidden(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67),X67)
        | X67 = k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66) )
      & ( esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67) != X62
        | ~ r2_hidden(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67),X67)
        | X67 = k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66) )
      & ( esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67) != X63
        | ~ r2_hidden(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67),X67)
        | X67 = k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66) )
      & ( esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67) != X64
        | ~ r2_hidden(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67),X67)
        | X67 = k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66) )
      & ( esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67) != X65
        | ~ r2_hidden(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67),X67)
        | X67 = k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66) )
      & ( esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67) != X66
        | ~ r2_hidden(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67),X67)
        | X67 = k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66) )
      & ( r2_hidden(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67),X67)
        | esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67) = X59
        | esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67) = X60
        | esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67) = X61
        | esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67) = X62
        | esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67) = X63
        | esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67) = X64
        | esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67) = X65
        | esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67) = X66
        | X67 = k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_43,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk6_0,X1),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_46,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_47,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk6_0,esk5_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_52,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).

cnf(c_0_54,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( X1 = X2 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_51,c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 0.19/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.38  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 0.19/0.38  fof(t12_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 0.19/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.38  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 0.19/0.38  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.19/0.38  fof(c_0_14, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))))&(r2_hidden(esk5_0,esk3_0)&k1_funct_1(esk6_0,esk5_0)!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.19/0.38  fof(c_0_15, plain, ![X18]:k2_tarski(X18,X18)=k1_tarski(X18), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.38  fof(c_0_16, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.38  fof(c_0_17, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.38  fof(c_0_18, plain, ![X24, X25, X26, X27]:k3_enumset1(X24,X24,X25,X26,X27)=k2_enumset1(X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.38  fof(c_0_19, plain, ![X28, X29, X30, X31, X32]:k4_enumset1(X28,X28,X29,X30,X31,X32)=k3_enumset1(X28,X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.38  fof(c_0_20, plain, ![X33, X34, X35, X36, X37, X38]:k5_enumset1(X33,X33,X34,X35,X36,X37,X38)=k4_enumset1(X33,X34,X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.38  fof(c_0_21, plain, ![X39, X40, X41, X42, X43, X44, X45]:k6_enumset1(X39,X39,X40,X41,X42,X43,X44,X45)=k5_enumset1(X39,X40,X41,X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.38  fof(c_0_22, plain, ![X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X13,X12)|X13=X11|X12!=k1_tarski(X11))&(X14!=X11|r2_hidden(X14,X12)|X12!=k1_tarski(X11)))&((~r2_hidden(esk1_2(X15,X16),X16)|esk1_2(X15,X16)!=X15|X16=k1_tarski(X15))&(r2_hidden(esk1_2(X15,X16),X16)|esk1_2(X15,X16)=X15|X16=k1_tarski(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.38  fof(c_0_23, plain, ![X72, X73, X74, X75]:(~v1_funct_1(X75)|~v1_funct_2(X75,X72,X73)|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X72,X73)))|(~r2_hidden(X74,X72)|(X73=k1_xboole_0|r2_hidden(k1_funct_1(X75,X74),X73)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_28, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_29, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_30, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_31, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  fof(c_0_33, plain, ![X69, X70, X71]:((k1_mcart_1(X69)=X70|~r2_hidden(X69,k2_zfmisc_1(k1_tarski(X70),X71)))&(r2_hidden(k2_mcart_1(X69),X71)|~r2_hidden(X69,k2_zfmisc_1(k1_tarski(X70),X71)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).
% 0.19/0.38  fof(c_0_34, plain, ![X46, X47]:((k2_zfmisc_1(X46,X47)!=k1_xboole_0|(X46=k1_xboole_0|X47=k1_xboole_0))&((X46!=k1_xboole_0|k2_zfmisc_1(X46,X47)=k1_xboole_0)&(X47!=k1_xboole_0|k2_zfmisc_1(X46,X47)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.38  cnf(c_0_35, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_36, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_40, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.38  cnf(c_0_41, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.38  fof(c_0_42, plain, ![X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59, X60, X61, X62, X63, X64, X65, X66, X67]:(((~r2_hidden(X57,X56)|(X57=X48|X57=X49|X57=X50|X57=X51|X57=X52|X57=X53|X57=X54|X57=X55)|X56!=k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55))&((((((((X58!=X48|r2_hidden(X58,X56)|X56!=k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55))&(X58!=X49|r2_hidden(X58,X56)|X56!=k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55)))&(X58!=X50|r2_hidden(X58,X56)|X56!=k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55)))&(X58!=X51|r2_hidden(X58,X56)|X56!=k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55)))&(X58!=X52|r2_hidden(X58,X56)|X56!=k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55)))&(X58!=X53|r2_hidden(X58,X56)|X56!=k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55)))&(X58!=X54|r2_hidden(X58,X56)|X56!=k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55)))&(X58!=X55|r2_hidden(X58,X56)|X56!=k6_enumset1(X48,X49,X50,X51,X52,X53,X54,X55))))&(((((((((esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67)!=X59|~r2_hidden(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67),X67)|X67=k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66))&(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67)!=X60|~r2_hidden(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67),X67)|X67=k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66)))&(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67)!=X61|~r2_hidden(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67),X67)|X67=k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66)))&(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67)!=X62|~r2_hidden(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67),X67)|X67=k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66)))&(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67)!=X63|~r2_hidden(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67),X67)|X67=k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66)))&(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67)!=X64|~r2_hidden(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67),X67)|X67=k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66)))&(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67)!=X65|~r2_hidden(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67),X67)|X67=k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66)))&(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67)!=X66|~r2_hidden(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67),X67)|X67=k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66)))&(r2_hidden(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67),X67)|(esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67)=X59|esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67)=X60|esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67)=X61|esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67)=X62|esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67)=X63|esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67)=X64|esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67)=X65|esk2_9(X59,X60,X61,X62,X63,X64,X65,X66,X67)=X66)|X67=k6_enumset1(X59,X60,X61,X62,X63,X64,X65,X66)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.19/0.38  cnf(c_0_43, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0|r2_hidden(k1_funct_1(esk6_0,X1),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39])])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_46, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.19/0.38  cnf(c_0_47, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_41])).
% 0.19/0.38  cnf(c_0_48, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.38  cnf(c_0_49, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_43])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0|r2_hidden(k1_funct_1(esk6_0,esk5_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_52, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.38  cnf(c_0_53, plain, (r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.19/0.38  cnf(c_0_55, plain, (X1=X2|~r2_hidden(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_52])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (r2_hidden(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (X1=X2), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_51, c_0_57]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 59
% 0.19/0.38  # Proof object clause steps            : 32
% 0.19/0.38  # Proof object formula steps           : 27
% 0.19/0.38  # Proof object conjectures             : 16
% 0.19/0.38  # Proof object clause conjectures      : 13
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 17
% 0.19/0.38  # Proof object initial formulas used   : 13
% 0.19/0.38  # Proof object generating inferences   : 7
% 0.19/0.38  # Proof object simplifying inferences  : 37
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 13
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 40
% 0.19/0.38  # Removed in clause preprocessing      : 7
% 0.19/0.38  # Initial clauses in saturation        : 33
% 0.19/0.38  # Processed clauses                    : 76
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 2
% 0.19/0.38  # ...remaining for further processing  : 74
% 0.19/0.38  # Other redundant clauses eliminated   : 22
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 10
% 0.19/0.38  # Backward-rewritten                   : 4
% 0.19/0.38  # Generated clauses                    : 123
% 0.19/0.38  # ...of the previous two non-trivial   : 89
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 109
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 22
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 14
% 0.19/0.38  #    Positive orientable unit clauses  : 11
% 0.19/0.38  #    Positive unorientable unit clauses: 1
% 0.19/0.38  #    Negative unit clauses             : 0
% 0.19/0.38  #    Non-unit-clauses                  : 2
% 0.19/0.38  # Current number of unprocessed clauses: 68
% 0.19/0.38  # ...number of literals in the above   : 229
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 54
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 90
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 70
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.19/0.38  # Unit Clause-clause subsumption calls : 24
% 0.19/0.38  # Rewrite failures with RHS unbound    : 72
% 0.19/0.38  # BW rewrite match attempts            : 130
% 0.19/0.38  # BW rewrite match successes           : 57
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 3295
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.032 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.036 s
% 0.19/0.38  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
