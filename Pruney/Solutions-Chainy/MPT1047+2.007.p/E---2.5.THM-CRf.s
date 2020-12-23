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
% DateTime   : Thu Dec  3 11:07:12 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 681 expanded)
%              Number of clauses        :   56 ( 269 expanded)
%              Number of leaves         :   15 ( 192 expanded)
%              Depth                    :   14
%              Number of atoms          :  306 (1634 expanded)
%              Number of equality atoms :  102 ( 719 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t164_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,k1_tarski(X2))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => k5_partfun1(X1,k1_tarski(X2),X3) = k1_tarski(X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).

fof(t143_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => r1_partfun1(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t132_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | v1_partfun1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(l44_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(t148_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ( v1_partfun1(X3,X1)
              & v1_partfun1(X4,X1)
              & r1_partfun1(X3,X4) )
           => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t158_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
         => ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t155_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r1_partfun1(X3,X4)
           => ( ( X2 = k1_xboole_0
                & X1 != k1_xboole_0 )
              | r2_hidden(X4,k5_partfun1(X1,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).

fof(c_0_15,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X9
        | X12 = X10
        | X11 != k2_tarski(X9,X10) )
      & ( X13 != X9
        | r2_hidden(X13,X11)
        | X11 != k2_tarski(X9,X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k2_tarski(X9,X10) )
      & ( esk2_3(X14,X15,X16) != X14
        | ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k2_tarski(X14,X15) )
      & ( esk2_3(X14,X15,X16) != X15
        | ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k2_tarski(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X16)
        | esk2_3(X14,X15,X16) = X14
        | esk2_3(X14,X15,X16) = X15
        | X16 = k2_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_16,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,k1_tarski(X2))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
           => k5_partfun1(X1,k1_tarski(X2),X3) = k1_tarski(X4) ) ) ),
    inference(assume_negation,[status(cth)],[t164_funct_2])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X35,X36,X37,X38] :
      ( ~ v1_funct_1(X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,k1_tarski(X36))))
      | ~ v1_funct_1(X38)
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,k1_tarski(X36))))
      | r1_partfun1(X37,X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_partfun1])])])).

fof(c_0_23,plain,(
    ! [X18] : k2_tarski(X18,X18) = k1_tarski(X18) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_24,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk4_0,k1_tarski(esk5_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))))
    & k5_partfun1(esk4_0,k1_tarski(esk5_0),esk6_0) != k1_tarski(esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

fof(c_0_26,plain,(
    ! [X32,X33,X34] :
      ( ( X33 = k1_xboole_0
        | v1_partfun1(X34,X32)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X32,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | ~ v1_funct_1(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( X32 != k1_xboole_0
        | v1_partfun1(X34,X32)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X32,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | ~ v1_funct_1(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).

fof(c_0_27,plain,(
    ! [X24,X25] :
      ( ( r2_hidden(esk3_2(X24,X25),X24)
        | X24 = k1_tarski(X25)
        | X24 = k1_xboole_0 )
      & ( esk3_2(X24,X25) != X25
        | X24 = k1_tarski(X25)
        | X24 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).

cnf(c_0_28,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X3,X3,X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( k5_partfun1(esk4_0,k1_tarski(esk5_0),esk6_0) != k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X29,X30,X31] :
      ( k2_zfmisc_1(k1_tarski(X29),k2_tarski(X30,X31)) = k2_tarski(k4_tarski(X29,X30),k4_tarski(X29,X31))
      & k2_zfmisc_1(k2_tarski(X29,X30),k1_tarski(X31)) = k2_tarski(k4_tarski(X29,X31),k4_tarski(X30,X31)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

fof(c_0_38,plain,(
    ! [X39,X40,X41,X42] :
      ( ~ v1_funct_1(X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | ~ v1_funct_1(X42)
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | ~ v1_partfun1(X41,X39)
      | ~ v1_partfun1(X42,X39)
      | ~ r1_partfun1(X41,X42)
      | X41 = X42 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_partfun1])])])).

cnf(c_0_39,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_29]),c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_29]),c_0_20]),c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_42,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_29]),c_0_20]),c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) != k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_29]),c_0_29]),c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | r2_hidden(esk3_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_29]),c_0_20]),c_0_21])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( X1 = X4
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X4,X2)
    | ~ r1_partfun1(X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( r1_partfun1(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_51,plain,
    ( ~ v1_xboole_0(k2_enumset1(X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0
    | v1_partfun1(esk7_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_40]),c_0_41])])).

cnf(c_0_53,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_54,plain,(
    ! [X47,X48,X49,X50] :
      ( ( v1_funct_1(X50)
        | ~ r2_hidden(X50,k5_partfun1(X47,X48,X49))
        | ~ v1_funct_1(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( v1_funct_2(X50,X47,X48)
        | ~ r2_hidden(X50,k5_partfun1(X47,X48,X49))
        | ~ v1_funct_1(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
        | ~ r2_hidden(X50,k5_partfun1(X47,X48,X49))
        | ~ v1_funct_1(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).

cnf(c_0_55,negated_conjecture,
    ( k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) = k1_xboole_0
    | r2_hidden(esk3_2(k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),X1),k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0))
    | k2_enumset1(X1,X1,X1,X1) != k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X3)) = k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_29]),c_0_20]),c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_21])).

fof(c_0_58,plain,(
    ! [X27,X28] :
      ( ( k2_zfmisc_1(X27,X28) != k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 )
      & ( X27 != k1_xboole_0
        | k2_zfmisc_1(X27,X28) = k1_xboole_0 )
      & ( X28 != k1_xboole_0
        | k2_zfmisc_1(X27,X28) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_59,negated_conjecture,
    ( X1 = esk7_0
    | ~ v1_partfun1(esk7_0,esk4_0)
    | ~ v1_partfun1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_40]),c_0_41])]),c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( v1_partfun1(esk7_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) = k1_xboole_0
    | r2_hidden(esk3_2(k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),esk7_0),k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_29]),c_0_20]),c_0_21])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_65,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_66,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_67,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_57])).

cnf(c_0_68,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( X1 = esk7_0
    | ~ v1_partfun1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_70,negated_conjecture,
    ( k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) = k1_xboole_0
    | m1_subset_1(esk3_2(k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64])])).

cnf(c_0_71,negated_conjecture,
    ( k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) = k1_xboole_0
    | v1_funct_1(esk3_2(k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_62]),c_0_63]),c_0_64])])).

cnf(c_0_72,negated_conjecture,
    ( k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) = k1_xboole_0
    | v1_funct_2(esk3_2(k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),esk7_0),esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_62]),c_0_63]),c_0_64])])).

cnf(c_0_73,plain,
    ( k2_enumset1(X1,X1,X1,X2) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_53])])).

cnf(c_0_74,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk3_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_75,negated_conjecture,
    ( esk3_2(k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),esk7_0) = esk7_0
    | k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) = k1_xboole_0
    | ~ v1_partfun1(esk3_2(k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),esk7_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) = k1_xboole_0
    | v1_partfun1(esk3_2(k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),esk7_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_72]),c_0_73]),c_0_71]),c_0_70])).

fof(c_0_77,plain,(
    ! [X43,X44,X45,X46] :
      ( ( X44 = k1_xboole_0
        | r2_hidden(X46,k5_partfun1(X43,X44,X45))
        | ~ r1_partfun1(X45,X46)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X43,X44)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | ~ v1_funct_1(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( X43 != k1_xboole_0
        | r2_hidden(X46,k5_partfun1(X43,X44,X45))
        | ~ r1_partfun1(X45,X46)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X43,X44)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | ~ v1_funct_1(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_2])])])])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | esk3_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_29]),c_0_20]),c_0_21])).

cnf(c_0_79,negated_conjecture,
    ( esk3_2(k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),esk7_0) = esk7_0
    | k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_80,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k5_partfun1(X3,X1,X4))
    | ~ r1_partfun1(X4,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_46])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r1_partfun1(esk6_0,X1)
    | ~ v1_funct_2(X1,esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_63]),c_0_64])]),c_0_73])).

cnf(c_0_83,negated_conjecture,
    ( r1_partfun1(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_63]),c_0_64])])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_45]),c_0_83]),c_0_40]),c_0_41])])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_84]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:50:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 2.38/2.57  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_URBAN_S0Y
% 2.38/2.57  # and selection function SelectMaxLComplexAvoidPosPred.
% 2.38/2.57  #
% 2.38/2.57  # Preprocessing time       : 0.041 s
% 2.38/2.57  
% 2.38/2.57  # Proof found!
% 2.38/2.57  # SZS status Theorem
% 2.38/2.57  # SZS output start CNFRefutation
% 2.38/2.57  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.38/2.57  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.38/2.57  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.38/2.57  fof(t164_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>k5_partfun1(X1,k1_tarski(X2),X3)=k1_tarski(X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_2)).
% 2.38/2.57  fof(t143_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>r1_partfun1(X3,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_partfun1)).
% 2.38/2.57  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.38/2.57  fof(t132_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 2.38/2.57  fof(l44_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 2.38/2.57  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.38/2.57  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 2.38/2.57  fof(t148_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_partfun1(X3,X1)&v1_partfun1(X4,X1))&r1_partfun1(X3,X4))=>X3=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 2.38/2.57  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.38/2.57  fof(t158_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(r2_hidden(X4,k5_partfun1(X1,X2,X3))=>((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_2)).
% 2.38/2.57  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.38/2.57  fof(t155_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_hidden(X4,k5_partfun1(X1,X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_2)).
% 2.38/2.57  fof(c_0_15, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X12,X11)|(X12=X9|X12=X10)|X11!=k2_tarski(X9,X10))&((X13!=X9|r2_hidden(X13,X11)|X11!=k2_tarski(X9,X10))&(X13!=X10|r2_hidden(X13,X11)|X11!=k2_tarski(X9,X10))))&(((esk2_3(X14,X15,X16)!=X14|~r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k2_tarski(X14,X15))&(esk2_3(X14,X15,X16)!=X15|~r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k2_tarski(X14,X15)))&(r2_hidden(esk2_3(X14,X15,X16),X16)|(esk2_3(X14,X15,X16)=X14|esk2_3(X14,X15,X16)=X15)|X16=k2_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 2.38/2.57  fof(c_0_16, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 2.38/2.57  fof(c_0_17, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 2.38/2.57  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>k5_partfun1(X1,k1_tarski(X2),X3)=k1_tarski(X4)))), inference(assume_negation,[status(cth)],[t164_funct_2])).
% 2.38/2.57  cnf(c_0_19, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.38/2.57  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.38/2.57  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.38/2.57  fof(c_0_22, plain, ![X35, X36, X37, X38]:(~v1_funct_1(X37)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,k1_tarski(X36))))|(~v1_funct_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,k1_tarski(X36))))|r1_partfun1(X37,X38))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_partfun1])])])).
% 2.38/2.57  fof(c_0_23, plain, ![X18]:k2_tarski(X18,X18)=k1_tarski(X18), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 2.38/2.57  fof(c_0_24, negated_conjecture, ((v1_funct_1(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk4_0,k1_tarski(esk5_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))))&k5_partfun1(esk4_0,k1_tarski(esk5_0),esk6_0)!=k1_tarski(esk7_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 2.38/2.57  cnf(c_0_25, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 2.38/2.57  fof(c_0_26, plain, ![X32, X33, X34]:((X33=k1_xboole_0|v1_partfun1(X34,X32)|(~v1_funct_1(X34)|~v1_funct_2(X34,X32,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))|(~v1_funct_1(X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&(X32!=k1_xboole_0|v1_partfun1(X34,X32)|(~v1_funct_1(X34)|~v1_funct_2(X34,X32,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))|(~v1_funct_1(X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).
% 2.38/2.57  fof(c_0_27, plain, ![X24, X25]:((r2_hidden(esk3_2(X24,X25),X24)|(X24=k1_tarski(X25)|X24=k1_xboole_0))&(esk3_2(X24,X25)!=X25|(X24=k1_tarski(X25)|X24=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).
% 2.38/2.57  cnf(c_0_28, plain, (r1_partfun1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.38/2.57  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.38/2.57  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.38/2.57  fof(c_0_31, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 2.38/2.57  cnf(c_0_32, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X3,X3,X1)), inference(er,[status(thm)],[c_0_25])).
% 2.38/2.57  cnf(c_0_33, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.38/2.57  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk7_0,esk4_0,k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.38/2.57  cnf(c_0_35, negated_conjecture, (k5_partfun1(esk4_0,k1_tarski(esk5_0),esk6_0)!=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.38/2.57  cnf(c_0_36, plain, (r2_hidden(esk3_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.38/2.57  fof(c_0_37, plain, ![X29, X30, X31]:(k2_zfmisc_1(k1_tarski(X29),k2_tarski(X30,X31))=k2_tarski(k4_tarski(X29,X30),k4_tarski(X29,X31))&k2_zfmisc_1(k2_tarski(X29,X30),k1_tarski(X31))=k2_tarski(k4_tarski(X29,X31),k4_tarski(X30,X31))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 2.38/2.57  fof(c_0_38, plain, ![X39, X40, X41, X42]:(~v1_funct_1(X41)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|(~v1_funct_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|(~v1_partfun1(X41,X39)|~v1_partfun1(X42,X39)|~r1_partfun1(X41,X42)|X41=X42))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_partfun1])])])).
% 2.38/2.57  cnf(c_0_39, plain, (r1_partfun1(X1,X4)|~v1_funct_1(X4)|~v1_funct_1(X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_29]), c_0_20]), c_0_20]), c_0_21]), c_0_21])).
% 2.38/2.57  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_29]), c_0_20]), c_0_21])).
% 2.38/2.57  cnf(c_0_41, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.38/2.57  cnf(c_0_42, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.38/2.57  cnf(c_0_43, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[c_0_32])).
% 2.38/2.57  cnf(c_0_44, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(cn,[status(thm)],[c_0_33])).
% 2.38/2.57  cnf(c_0_45, negated_conjecture, (v1_funct_2(esk7_0,esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_29]), c_0_20]), c_0_21])).
% 2.38/2.57  cnf(c_0_46, negated_conjecture, (k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)!=k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_29]), c_0_29]), c_0_20]), c_0_20]), c_0_21]), c_0_21])).
% 2.38/2.57  cnf(c_0_47, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|r2_hidden(esk3_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_29]), c_0_20]), c_0_21])).
% 2.38/2.57  cnf(c_0_48, plain, (k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.38/2.57  cnf(c_0_49, plain, (X1=X4|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_partfun1(X1,X2)|~v1_partfun1(X4,X2)|~r1_partfun1(X1,X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.38/2.57  cnf(c_0_50, negated_conjecture, (r1_partfun1(X1,esk7_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 2.38/2.57  cnf(c_0_51, plain, (~v1_xboole_0(k2_enumset1(X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 2.38/2.57  cnf(c_0_52, negated_conjecture, (k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0|v1_partfun1(esk7_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_40]), c_0_41])])).
% 2.38/2.57  cnf(c_0_53, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 2.38/2.57  fof(c_0_54, plain, ![X47, X48, X49, X50]:(((v1_funct_1(X50)|~r2_hidden(X50,k5_partfun1(X47,X48,X49))|(~v1_funct_1(X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))&(v1_funct_2(X50,X47,X48)|~r2_hidden(X50,k5_partfun1(X47,X48,X49))|(~v1_funct_1(X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))))&(m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|~r2_hidden(X50,k5_partfun1(X47,X48,X49))|(~v1_funct_1(X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).
% 2.38/2.57  cnf(c_0_55, negated_conjecture, (k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)=k1_xboole_0|r2_hidden(esk3_2(k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),X1),k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0))|k2_enumset1(X1,X1,X1,X1)!=k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 2.38/2.57  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.38/2.57  cnf(c_0_57, plain, (k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X3))=k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_29]), c_0_20]), c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_21])).
% 2.38/2.57  fof(c_0_58, plain, ![X27, X28]:((k2_zfmisc_1(X27,X28)!=k1_xboole_0|(X27=k1_xboole_0|X28=k1_xboole_0))&((X27!=k1_xboole_0|k2_zfmisc_1(X27,X28)=k1_xboole_0)&(X28!=k1_xboole_0|k2_zfmisc_1(X27,X28)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 2.38/2.57  cnf(c_0_59, negated_conjecture, (X1=esk7_0|~v1_partfun1(esk7_0,esk4_0)|~v1_partfun1(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_40]), c_0_41])]), c_0_50])).
% 2.38/2.57  cnf(c_0_60, negated_conjecture, (v1_partfun1(esk7_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 2.38/2.57  cnf(c_0_61, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 2.38/2.57  cnf(c_0_62, negated_conjecture, (k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)=k1_xboole_0|r2_hidden(esk3_2(k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),esk7_0),k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0))), inference(er,[status(thm)],[c_0_55])).
% 2.38/2.57  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_29]), c_0_20]), c_0_21])).
% 2.38/2.57  cnf(c_0_64, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.38/2.57  cnf(c_0_65, plain, (v1_funct_1(X1)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 2.38/2.57  cnf(c_0_66, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 2.38/2.57  cnf(c_0_67, plain, (~v1_xboole_0(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X3)))), inference(spm,[status(thm)],[c_0_51, c_0_57])).
% 2.38/2.57  cnf(c_0_68, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_58])).
% 2.38/2.57  cnf(c_0_69, negated_conjecture, (X1=esk7_0|~v1_partfun1(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])])).
% 2.38/2.57  cnf(c_0_70, negated_conjecture, (k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)=k1_xboole_0|m1_subset_1(esk3_2(k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64])])).
% 2.38/2.57  cnf(c_0_71, negated_conjecture, (k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)=k1_xboole_0|v1_funct_1(esk3_2(k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_62]), c_0_63]), c_0_64])])).
% 2.38/2.57  cnf(c_0_72, negated_conjecture, (k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)=k1_xboole_0|v1_funct_2(esk3_2(k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),esk7_0),esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_62]), c_0_63]), c_0_64])])).
% 2.38/2.57  cnf(c_0_73, plain, (k2_enumset1(X1,X1,X1,X2)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_53])])).
% 2.38/2.57  cnf(c_0_74, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk3_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.38/2.57  cnf(c_0_75, negated_conjecture, (esk3_2(k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),esk7_0)=esk7_0|k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)=k1_xboole_0|~v1_partfun1(esk3_2(k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),esk7_0),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 2.38/2.57  cnf(c_0_76, negated_conjecture, (k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)=k1_xboole_0|v1_partfun1(esk3_2(k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),esk7_0),esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_72]), c_0_73]), c_0_71]), c_0_70])).
% 2.38/2.57  fof(c_0_77, plain, ![X43, X44, X45, X46]:((X44=k1_xboole_0|r2_hidden(X46,k5_partfun1(X43,X44,X45))|~r1_partfun1(X45,X46)|(~v1_funct_1(X46)|~v1_funct_2(X46,X43,X44)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44))))|(~v1_funct_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))&(X43!=k1_xboole_0|r2_hidden(X46,k5_partfun1(X43,X44,X45))|~r1_partfun1(X45,X46)|(~v1_funct_1(X46)|~v1_funct_2(X46,X43,X44)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44))))|(~v1_funct_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_2])])])])).
% 2.38/2.57  cnf(c_0_78, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|esk3_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_29]), c_0_20]), c_0_21])).
% 2.38/2.57  cnf(c_0_79, negated_conjecture, (esk3_2(k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0),esk7_0)=esk7_0|k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 2.38/2.57  cnf(c_0_80, plain, (X1=k1_xboole_0|r2_hidden(X2,k5_partfun1(X3,X1,X4))|~r1_partfun1(X4,X2)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 2.38/2.57  cnf(c_0_81, negated_conjecture, (k5_partfun1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_46])).
% 2.38/2.57  cnf(c_0_82, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~r1_partfun1(esk6_0,X1)|~v1_funct_2(X1,esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))|~v1_funct_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_63]), c_0_64])]), c_0_73])).
% 2.38/2.57  cnf(c_0_83, negated_conjecture, (r1_partfun1(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_63]), c_0_64])])).
% 2.38/2.57  cnf(c_0_84, negated_conjecture, (r2_hidden(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_45]), c_0_83]), c_0_40]), c_0_41])])).
% 2.38/2.57  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_84]), c_0_53])]), ['proof']).
% 2.38/2.57  # SZS output end CNFRefutation
% 2.38/2.57  # Proof object total steps             : 86
% 2.38/2.57  # Proof object clause steps            : 56
% 2.38/2.57  # Proof object formula steps           : 30
% 2.38/2.57  # Proof object conjectures             : 31
% 2.38/2.57  # Proof object clause conjectures      : 28
% 2.38/2.57  # Proof object formula conjectures     : 3
% 2.38/2.57  # Proof object initial clauses used    : 23
% 2.38/2.57  # Proof object initial formulas used   : 15
% 2.38/2.57  # Proof object generating inferences   : 21
% 2.38/2.57  # Proof object simplifying inferences  : 78
% 2.38/2.57  # Training examples: 0 positive, 0 negative
% 2.38/2.57  # Parsed axioms                        : 15
% 2.38/2.57  # Removed by relevancy pruning/SinE    : 0
% 2.38/2.57  # Initial clauses                      : 34
% 2.38/2.57  # Removed in clause preprocessing      : 3
% 2.38/2.57  # Initial clauses in saturation        : 31
% 2.38/2.57  # Processed clauses                    : 908
% 2.38/2.57  # ...of these trivial                  : 5
% 2.38/2.57  # ...subsumed                          : 427
% 2.38/2.57  # ...remaining for further processing  : 476
% 2.38/2.57  # Other redundant clauses eliminated   : 1057
% 2.38/2.57  # Clauses deleted for lack of memory   : 0
% 2.38/2.57  # Backward-subsumed                    : 20
% 2.38/2.57  # Backward-rewritten                   : 22
% 2.38/2.57  # Generated clauses                    : 89705
% 2.38/2.57  # ...of the previous two non-trivial   : 87962
% 2.38/2.57  # Contextual simplify-reflections      : 30
% 2.38/2.57  # Paramodulations                      : 88501
% 2.38/2.57  # Factorizations                       : 122
% 2.38/2.57  # Equation resolutions                 : 1082
% 2.38/2.57  # Propositional unsat checks           : 0
% 2.38/2.57  #    Propositional check models        : 0
% 2.38/2.57  #    Propositional check unsatisfiable : 0
% 2.38/2.57  #    Propositional clauses             : 0
% 2.38/2.57  #    Propositional clauses after purity: 0
% 2.38/2.57  #    Propositional unsat core size     : 0
% 2.38/2.57  #    Propositional preprocessing time  : 0.000
% 2.38/2.57  #    Propositional encoding time       : 0.000
% 2.38/2.57  #    Propositional solver time         : 0.000
% 2.38/2.57  #    Success case prop preproc time    : 0.000
% 2.38/2.57  #    Success case prop encoding time   : 0.000
% 2.38/2.57  #    Success case prop solver time     : 0.000
% 2.38/2.57  # Current number of processed clauses  : 432
% 2.38/2.57  #    Positive orientable unit clauses  : 33
% 2.38/2.57  #    Positive unorientable unit clauses: 0
% 2.38/2.57  #    Negative unit clauses             : 11
% 2.38/2.57  #    Non-unit-clauses                  : 388
% 2.38/2.57  # Current number of unprocessed clauses: 87011
% 2.38/2.57  # ...number of literals in the above   : 724866
% 2.38/2.57  # Current number of archived formulas  : 0
% 2.38/2.57  # Current number of archived clauses   : 45
% 2.38/2.57  # Clause-clause subsumption calls (NU) : 36671
% 2.38/2.57  # Rec. Clause-clause subsumption calls : 3792
% 2.38/2.57  # Non-unit clause-clause subsumptions  : 346
% 2.38/2.57  # Unit Clause-clause subsumption calls : 405
% 2.38/2.57  # Rewrite failures with RHS unbound    : 0
% 2.38/2.57  # BW rewrite match attempts            : 43
% 2.38/2.57  # BW rewrite match successes           : 3
% 2.38/2.57  # Condensation attempts                : 0
% 2.38/2.57  # Condensation successes               : 0
% 2.38/2.57  # Termbank termtop insertions          : 2933597
% 2.38/2.58  
% 2.38/2.58  # -------------------------------------------------
% 2.38/2.58  # User time                : 2.187 s
% 2.38/2.58  # System time              : 0.050 s
% 2.38/2.58  # Total time               : 2.237 s
% 2.38/2.58  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
