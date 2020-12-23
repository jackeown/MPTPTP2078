%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:12 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 947 expanded)
%              Number of clauses        :   71 ( 382 expanded)
%              Number of leaves         :   14 ( 262 expanded)
%              Depth                    :   14
%              Number of atoms          :  332 (2224 expanded)
%              Number of equality atoms :  110 (1045 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t129_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))
    <=> ( r2_hidden(X1,X3)
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t143_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => r1_partfun1(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

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

fof(t131_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X1 != X2
     => ( r1_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X4))
        & r1_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X4,k1_tarski(X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_zfmisc_1)).

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

fof(t16_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
        & X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,k1_tarski(X2))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
           => k5_partfun1(X1,k1_tarski(X2),X3) = k1_tarski(X4) ) ) ),
    inference(assume_negation,[status(cth)],[t164_funct_2])).

fof(c_0_15,plain,(
    ! [X16,X17,X18,X19] :
      ( ( r2_hidden(X16,X18)
        | ~ r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(X18,k1_tarski(X19))) )
      & ( X17 = X19
        | ~ r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(X18,k1_tarski(X19))) )
      & ( ~ r2_hidden(X16,X18)
        | X17 != X19
        | r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(X18,k1_tarski(X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).

fof(c_0_16,plain,(
    ! [X5] : k2_tarski(X5,X5) = k1_tarski(X5) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X6,X7) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X8,X9,X10] : k2_enumset1(X8,X8,X9,X10) = k1_enumset1(X8,X9,X10) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X26,X27,X28] :
      ( ( X27 = k1_xboole_0
        | v1_partfun1(X28,X26)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( X26 != k1_xboole_0
        | v1_partfun1(X28,X26)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).

fof(c_0_20,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0))))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0))))
    & k5_partfun1(esk2_0,k1_tarski(esk3_0),esk4_0) != k1_tarski(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_21,plain,(
    ! [X11,X12] :
      ( ( r2_hidden(esk1_2(X11,X12),X11)
        | X11 = k1_tarski(X12)
        | X11 = k1_xboole_0 )
      & ( esk1_2(X11,X12) != X12
        | X11 = k1_tarski(X12)
        | X11 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).

fof(c_0_22,plain,(
    ! [X14,X15] :
      ( ( k2_zfmisc_1(X14,X15) != k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k1_tarski(X4)))
    | ~ r2_hidden(X1,X2)
    | X3 != X4 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( k5_partfun1(esk2_0,k1_tarski(esk3_0),esk4_0) != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k2_enumset1(X4,X4,X4,X4)))
    | X3 != X4
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])).

fof(c_0_35,plain,(
    ! [X29,X30,X31,X32] :
      ( ~ v1_funct_1(X31)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,k1_tarski(X30))))
      | ~ v1_funct_1(X32)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,k1_tarski(X30))))
      | r1_partfun1(X31,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_partfun1])])])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,negated_conjecture,
    ( k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) != k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_43,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k2_enumset1(X2,X2,X2,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0
    | v1_partfun1(esk5_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) = k1_xboole_0
    | r2_hidden(esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),X1),k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))
    | k2_enumset1(X1,X1,X1,X1) != k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( r2_hidden(k4_tarski(X1,X2),k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_44])).

fof(c_0_52,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ v1_funct_1(X35)
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | ~ v1_funct_1(X36)
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | ~ v1_partfun1(X35,X33)
      | ~ v1_partfun1(X36,X33)
      | ~ r1_partfun1(X35,X36)
      | X35 = X36 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_partfun1])])])).

cnf(c_0_53,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_26]),c_0_26])).

fof(c_0_54,plain,(
    ! [X41,X42,X43,X44] :
      ( ( v1_funct_1(X44)
        | ~ r2_hidden(X44,k5_partfun1(X41,X42,X43))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( v1_funct_2(X44,X41,X42)
        | ~ r2_hidden(X44,k5_partfun1(X41,X42,X43))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ r2_hidden(X44,k5_partfun1(X41,X42,X43))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_56,negated_conjecture,
    ( v1_partfun1(esk5_0,esk2_0)
    | r2_hidden(k4_tarski(X1,esk3_0),k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_47]),c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) = k1_xboole_0
    | r2_hidden(esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0),k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X1,X2),X1)
    | k2_enumset1(X2,X2,X2,X2) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_42])).

cnf(c_0_60,plain,
    ( X1 = X4
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X4,X2)
    | ~ r1_partfun1(X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( r1_partfun1(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_37]),c_0_39])])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_65,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) = k1_xboole_0
    | v1_partfun1(esk5_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_partfun1(esk5_0,esk2_0)
    | r2_hidden(esk1_2(X1,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_47])).

cnf(c_0_68,negated_conjecture,
    ( X1 = esk5_0
    | ~ v1_partfun1(esk5_0,esk2_0)
    | ~ v1_partfun1(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))))
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_37]),c_0_39])]),c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) = k1_xboole_0
    | m1_subset_1(esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_57]),c_0_63]),c_0_64])])).

cnf(c_0_70,negated_conjecture,
    ( k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) = k1_xboole_0
    | v1_funct_1(esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_57]),c_0_63]),c_0_64])])).

cnf(c_0_71,negated_conjecture,
    ( v1_partfun1(esk5_0,esk2_0)
    | k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_partfun1(esk5_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_67]),c_0_58])).

cnf(c_0_73,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_74,plain,(
    ! [X20,X21,X22,X23] :
      ( ( r1_xboole_0(k2_zfmisc_1(k1_tarski(X20),X22),k2_zfmisc_1(k1_tarski(X21),X23))
        | X20 = X21 )
      & ( r1_xboole_0(k2_zfmisc_1(X22,k1_tarski(X20)),k2_zfmisc_1(X23,k1_tarski(X21)))
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t131_zfmisc_1])])])).

fof(c_0_75,plain,(
    ! [X37,X38,X39,X40] :
      ( ( X38 = k1_xboole_0
        | r2_hidden(X40,k5_partfun1(X37,X38,X39))
        | ~ r1_partfun1(X39,X40)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X37,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
        | ~ v1_funct_1(X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X37 != k1_xboole_0
        | r2_hidden(X40,k5_partfun1(X37,X38,X39))
        | ~ r1_partfun1(X39,X40)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X37,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
        | ~ v1_funct_1(X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_2])])])])).

cnf(c_0_76,negated_conjecture,
    ( esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0) = esk5_0
    | k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) = k1_xboole_0
    | ~ v1_partfun1(esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0),esk2_0)
    | ~ v1_partfun1(esk5_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( v1_partfun1(esk5_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) = k1_xboole_0
    | v1_funct_2(esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0),esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_57]),c_0_63]),c_0_64])])).

cnf(c_0_79,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,k1_tarski(X2)),k2_zfmisc_1(X3,k1_tarski(X4)))
    | X2 = X4 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_80,plain,(
    ! [X24,X25] :
      ( ~ r1_xboole_0(k1_tarski(X24),k1_tarski(X25))
      | X24 != X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_zfmisc_1])])).

cnf(c_0_81,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k5_partfun1(X3,X1,X4))
    | ~ r1_partfun1(X4,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_82,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk1_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_83,negated_conjecture,
    ( esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0) = esk5_0
    | k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) = k1_xboole_0
    | ~ v1_partfun1(esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_84,negated_conjecture,
    ( k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) = k1_xboole_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0
    | v1_partfun1(esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_69]),c_0_70]),c_0_78])).

cnf(c_0_85,plain,
    ( X2 = X4
    | r1_xboole_0(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2)),k2_zfmisc_1(X3,k2_enumset1(X4,X4,X4,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_86,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0
    | r2_hidden(X1,k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))
    | ~ r1_partfun1(esk4_0,X1)
    | ~ v1_funct_2(X1,esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_63]),c_0_64])])).

cnf(c_0_88,negated_conjecture,
    ( r1_partfun1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_63]),c_0_64])])).

cnf(c_0_89,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | esk1_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_90,negated_conjecture,
    ( esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0) = esk5_0
    | k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) = k1_xboole_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_91,plain,
    ( X1 = X2
    | r1_xboole_0(k2_zfmisc_1(X3,k2_enumset1(X1,X1,X1,X1)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_44])).

cnf(c_0_92,plain,
    ( X1 != X2
    | ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_93,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0
    | r2_hidden(esk5_0,k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_37]),c_0_88]),c_0_38]),c_0_39])])).

cnf(c_0_94,negated_conjecture,
    ( k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) = k1_xboole_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_41])).

cnf(c_0_95,plain,
    ( X1 = X2
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_44])).

cnf(c_0_96,plain,
    ( ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_92])).

cnf(c_0_97,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_58])).

cnf(c_0_98,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_95])])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:18:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.46  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.46  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.46  #
% 0.20/0.46  # Preprocessing time       : 0.028 s
% 0.20/0.46  # Presaturation interreduction done
% 0.20/0.46  
% 0.20/0.46  # Proof found!
% 0.20/0.46  # SZS status Theorem
% 0.20/0.46  # SZS output start CNFRefutation
% 0.20/0.46  fof(t164_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>k5_partfun1(X1,k1_tarski(X2),X3)=k1_tarski(X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_2)).
% 0.20/0.46  fof(t129_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))<=>(r2_hidden(X1,X3)&X2=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 0.20/0.46  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.46  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.46  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.46  fof(t132_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 0.20/0.46  fof(l44_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 0.20/0.46  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.46  fof(t143_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>r1_partfun1(X3,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_partfun1)).
% 0.20/0.46  fof(t148_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_partfun1(X3,X1)&v1_partfun1(X4,X1))&r1_partfun1(X3,X4))=>X3=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 0.20/0.46  fof(t158_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(r2_hidden(X4,k5_partfun1(X1,X2,X3))=>((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_2)).
% 0.20/0.46  fof(t131_zfmisc_1, axiom, ![X1, X2, X3, X4]:(X1!=X2=>(r1_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X4))&r1_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X4,k1_tarski(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_zfmisc_1)).
% 0.20/0.46  fof(t155_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_hidden(X4,k5_partfun1(X1,X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_2)).
% 0.20/0.46  fof(t16_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),k1_tarski(X2))&X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 0.20/0.46  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>k5_partfun1(X1,k1_tarski(X2),X3)=k1_tarski(X4)))), inference(assume_negation,[status(cth)],[t164_funct_2])).
% 0.20/0.46  fof(c_0_15, plain, ![X16, X17, X18, X19]:(((r2_hidden(X16,X18)|~r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(X18,k1_tarski(X19))))&(X17=X19|~r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(X18,k1_tarski(X19)))))&(~r2_hidden(X16,X18)|X17!=X19|r2_hidden(k4_tarski(X16,X17),k2_zfmisc_1(X18,k1_tarski(X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).
% 0.20/0.46  fof(c_0_16, plain, ![X5]:k2_tarski(X5,X5)=k1_tarski(X5), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.46  fof(c_0_17, plain, ![X6, X7]:k1_enumset1(X6,X6,X7)=k2_tarski(X6,X7), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.46  fof(c_0_18, plain, ![X8, X9, X10]:k2_enumset1(X8,X8,X9,X10)=k1_enumset1(X8,X9,X10), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.46  fof(c_0_19, plain, ![X26, X27, X28]:((X27=k1_xboole_0|v1_partfun1(X28,X26)|(~v1_funct_1(X28)|~v1_funct_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))|(~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))&(X26!=k1_xboole_0|v1_partfun1(X28,X26)|(~v1_funct_1(X28)|~v1_funct_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))|(~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).
% 0.20/0.46  fof(c_0_20, negated_conjecture, ((v1_funct_1(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))))&k5_partfun1(esk2_0,k1_tarski(esk3_0),esk4_0)!=k1_tarski(esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.20/0.46  fof(c_0_21, plain, ![X11, X12]:((r2_hidden(esk1_2(X11,X12),X11)|(X11=k1_tarski(X12)|X11=k1_xboole_0))&(esk1_2(X11,X12)!=X12|(X11=k1_tarski(X12)|X11=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).
% 0.20/0.46  fof(c_0_22, plain, ![X14, X15]:((k2_zfmisc_1(X14,X15)!=k1_xboole_0|(X14=k1_xboole_0|X15=k1_xboole_0))&((X14!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0)&(X15!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.46  cnf(c_0_23, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k1_tarski(X4)))|~r2_hidden(X1,X2)|X3!=X4), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.46  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.46  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.46  cnf(c_0_27, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_29, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_30, negated_conjecture, (k5_partfun1(esk2_0,k1_tarski(esk3_0),esk4_0)!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_31, plain, (r2_hidden(esk1_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.46  cnf(c_0_32, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  cnf(c_0_33, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.46  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k2_enumset1(X4,X4,X4,X4)))|X3!=X4|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])).
% 0.20/0.46  fof(c_0_35, plain, ![X29, X30, X31, X32]:(~v1_funct_1(X31)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,k1_tarski(X30))))|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,k1_tarski(X30))))|r1_partfun1(X31,X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_partfun1])])])).
% 0.20/0.46  cnf(c_0_36, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(cn,[status(thm)],[c_0_27])).
% 0.20/0.46  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_24]), c_0_25]), c_0_26])).
% 0.20/0.46  cnf(c_0_38, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_24]), c_0_25]), c_0_26])).
% 0.20/0.46  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_40, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.46  cnf(c_0_41, negated_conjecture, (k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)!=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.20/0.46  cnf(c_0_42, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|r2_hidden(esk1_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_24]), c_0_25]), c_0_26])).
% 0.20/0.46  cnf(c_0_43, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_24]), c_0_25]), c_0_26])).
% 0.20/0.46  cnf(c_0_44, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_33])).
% 0.20/0.46  cnf(c_0_45, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k2_enumset1(X2,X2,X2,X2)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_34])).
% 0.20/0.46  cnf(c_0_46, plain, (r1_partfun1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.46  cnf(c_0_47, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0|v1_partfun1(esk5_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39])])).
% 0.20/0.46  cnf(c_0_48, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_40])).
% 0.20/0.46  cnf(c_0_49, negated_conjecture, (k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)=k1_xboole_0|r2_hidden(esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),X1),k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))|k2_enumset1(X1,X1,X1,X1)!=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.46  cnf(c_0_50, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.46  cnf(c_0_51, plain, (r2_hidden(k4_tarski(X1,X2),k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_44])).
% 0.20/0.46  fof(c_0_52, plain, ![X33, X34, X35, X36]:(~v1_funct_1(X35)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|(~v1_funct_1(X36)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|(~v1_partfun1(X35,X33)|~v1_partfun1(X36,X33)|~r1_partfun1(X35,X36)|X35=X36))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_partfun1])])])).
% 0.20/0.46  cnf(c_0_53, plain, (r1_partfun1(X1,X4)|~v1_funct_1(X4)|~v1_funct_1(X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.20/0.46  fof(c_0_54, plain, ![X41, X42, X43, X44]:(((v1_funct_1(X44)|~r2_hidden(X44,k5_partfun1(X41,X42,X43))|(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))&(v1_funct_2(X44,X41,X42)|~r2_hidden(X44,k5_partfun1(X41,X42,X43))|(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))))&(m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|~r2_hidden(X44,k5_partfun1(X41,X42,X43))|(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).
% 0.20/0.46  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_56, negated_conjecture, (v1_partfun1(esk5_0,esk2_0)|r2_hidden(k4_tarski(X1,esk3_0),k1_xboole_0)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_47]), c_0_48])).
% 0.20/0.46  cnf(c_0_57, negated_conjecture, (k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)=k1_xboole_0|r2_hidden(esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0),k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))), inference(er,[status(thm)],[c_0_49])).
% 0.20/0.46  cnf(c_0_58, plain, (X1=X2|~r2_hidden(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.46  cnf(c_0_59, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(X1,X2),X1)|k2_enumset1(X2,X2,X2,X2)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_42])).
% 0.20/0.46  cnf(c_0_60, plain, (X1=X4|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_partfun1(X1,X2)|~v1_partfun1(X4,X2)|~r1_partfun1(X1,X4)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.46  cnf(c_0_61, negated_conjecture, (r1_partfun1(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_37]), c_0_39])])).
% 0.20/0.46  cnf(c_0_62, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.46  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_24]), c_0_25]), c_0_26])).
% 0.20/0.46  cnf(c_0_64, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_65, plain, (v1_funct_1(X1)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.46  cnf(c_0_66, negated_conjecture, (k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)=k1_xboole_0|v1_partfun1(esk5_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.20/0.46  cnf(c_0_67, negated_conjecture, (X1=k1_xboole_0|v1_partfun1(esk5_0,esk2_0)|r2_hidden(esk1_2(X1,esk3_0),X1)), inference(spm,[status(thm)],[c_0_59, c_0_47])).
% 0.20/0.46  cnf(c_0_68, negated_conjecture, (X1=esk5_0|~v1_partfun1(esk5_0,esk2_0)|~v1_partfun1(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))))|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_37]), c_0_39])]), c_0_61])).
% 0.20/0.46  cnf(c_0_69, negated_conjecture, (k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)=k1_xboole_0|m1_subset_1(esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_57]), c_0_63]), c_0_64])])).
% 0.20/0.46  cnf(c_0_70, negated_conjecture, (k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)=k1_xboole_0|v1_funct_1(esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_57]), c_0_63]), c_0_64])])).
% 0.20/0.46  cnf(c_0_71, negated_conjecture, (v1_partfun1(esk5_0,esk2_0)|k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_66])).
% 0.20/0.46  cnf(c_0_72, negated_conjecture, (X1=k1_xboole_0|v1_partfun1(esk5_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_67]), c_0_58])).
% 0.20/0.46  cnf(c_0_73, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.46  fof(c_0_74, plain, ![X20, X21, X22, X23]:((r1_xboole_0(k2_zfmisc_1(k1_tarski(X20),X22),k2_zfmisc_1(k1_tarski(X21),X23))|X20=X21)&(r1_xboole_0(k2_zfmisc_1(X22,k1_tarski(X20)),k2_zfmisc_1(X23,k1_tarski(X21)))|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t131_zfmisc_1])])])).
% 0.20/0.46  fof(c_0_75, plain, ![X37, X38, X39, X40]:((X38=k1_xboole_0|r2_hidden(X40,k5_partfun1(X37,X38,X39))|~r1_partfun1(X39,X40)|(~v1_funct_1(X40)|~v1_funct_2(X40,X37,X38)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))|(~v1_funct_1(X39)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))&(X37!=k1_xboole_0|r2_hidden(X40,k5_partfun1(X37,X38,X39))|~r1_partfun1(X39,X40)|(~v1_funct_1(X40)|~v1_funct_2(X40,X37,X38)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))|(~v1_funct_1(X39)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_2])])])])).
% 0.20/0.46  cnf(c_0_76, negated_conjecture, (esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0)=esk5_0|k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)=k1_xboole_0|~v1_partfun1(esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0),esk2_0)|~v1_partfun1(esk5_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 0.20/0.46  cnf(c_0_77, negated_conjecture, (v1_partfun1(esk5_0,esk2_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.46  cnf(c_0_78, negated_conjecture, (k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)=k1_xboole_0|v1_funct_2(esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0),esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_57]), c_0_63]), c_0_64])])).
% 0.20/0.46  cnf(c_0_79, plain, (r1_xboole_0(k2_zfmisc_1(X1,k1_tarski(X2)),k2_zfmisc_1(X3,k1_tarski(X4)))|X2=X4), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.46  fof(c_0_80, plain, ![X24, X25]:(~r1_xboole_0(k1_tarski(X24),k1_tarski(X25))|X24!=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_zfmisc_1])])).
% 0.20/0.46  cnf(c_0_81, plain, (X1=k1_xboole_0|r2_hidden(X2,k5_partfun1(X3,X1,X4))|~r1_partfun1(X4,X2)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.46  cnf(c_0_82, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk1_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.46  cnf(c_0_83, negated_conjecture, (esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0)=esk5_0|k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)=k1_xboole_0|~v1_partfun1(esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77])])).
% 0.20/0.46  cnf(c_0_84, negated_conjecture, (k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)=k1_xboole_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0|v1_partfun1(esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0),esk2_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_69]), c_0_70]), c_0_78])).
% 0.20/0.46  cnf(c_0_85, plain, (X2=X4|r1_xboole_0(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2)),k2_zfmisc_1(X3,k2_enumset1(X4,X4,X4,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.20/0.46  cnf(c_0_86, plain, (~r1_xboole_0(k1_tarski(X1),k1_tarski(X2))|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.46  cnf(c_0_87, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0|r2_hidden(X1,k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))|~r1_partfun1(esk4_0,X1)|~v1_funct_2(X1,esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_63]), c_0_64])])).
% 0.20/0.46  cnf(c_0_88, negated_conjecture, (r1_partfun1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_63]), c_0_64])])).
% 0.20/0.46  cnf(c_0_89, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|esk1_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_24]), c_0_25]), c_0_26])).
% 0.20/0.46  cnf(c_0_90, negated_conjecture, (esk1_2(k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),esk5_0)=esk5_0|k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)=k1_xboole_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.20/0.46  cnf(c_0_91, plain, (X1=X2|r1_xboole_0(k2_zfmisc_1(X3,k2_enumset1(X1,X1,X1,X1)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_85, c_0_44])).
% 0.20/0.46  cnf(c_0_92, plain, (X1!=X2|~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.20/0.46  cnf(c_0_93, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0|r2_hidden(esk5_0,k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_37]), c_0_88]), c_0_38]), c_0_39])])).
% 0.20/0.46  cnf(c_0_94, negated_conjecture, (k5_partfun1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)=k1_xboole_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_41])).
% 0.20/0.46  cnf(c_0_95, plain, (X1=X2|r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_91, c_0_44])).
% 0.20/0.46  cnf(c_0_96, plain, (~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_92])).
% 0.20/0.46  cnf(c_0_97, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_58])).
% 0.20/0.46  cnf(c_0_98, negated_conjecture, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_95])])).
% 0.20/0.46  cnf(c_0_99, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])]), ['proof']).
% 0.20/0.46  # SZS output end CNFRefutation
% 0.20/0.46  # Proof object total steps             : 100
% 0.20/0.46  # Proof object clause steps            : 71
% 0.20/0.46  # Proof object formula steps           : 29
% 0.20/0.46  # Proof object conjectures             : 38
% 0.20/0.46  # Proof object clause conjectures      : 35
% 0.20/0.46  # Proof object formula conjectures     : 3
% 0.20/0.46  # Proof object initial clauses used    : 24
% 0.20/0.46  # Proof object initial formulas used   : 14
% 0.20/0.46  # Proof object generating inferences   : 30
% 0.20/0.46  # Proof object simplifying inferences  : 88
% 0.20/0.46  # Training examples: 0 positive, 0 negative
% 0.20/0.46  # Parsed axioms                        : 14
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 29
% 0.20/0.46  # Removed in clause preprocessing      : 3
% 0.20/0.46  # Initial clauses in saturation        : 26
% 0.20/0.46  # Processed clauses                    : 293
% 0.20/0.46  # ...of these trivial                  : 4
% 0.20/0.46  # ...subsumed                          : 57
% 0.20/0.46  # ...remaining for further processing  : 232
% 0.20/0.46  # Other redundant clauses eliminated   : 95
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 42
% 0.20/0.46  # Backward-rewritten                   : 80
% 0.20/0.46  # Generated clauses                    : 3549
% 0.20/0.46  # ...of the previous two non-trivial   : 3246
% 0.20/0.46  # Contextual simplify-reflections      : 20
% 0.20/0.46  # Paramodulations                      : 3439
% 0.20/0.46  # Factorizations                       : 14
% 0.20/0.46  # Equation resolutions                 : 96
% 0.20/0.46  # Propositional unsat checks           : 0
% 0.20/0.46  #    Propositional check models        : 0
% 0.20/0.46  #    Propositional check unsatisfiable : 0
% 0.20/0.46  #    Propositional clauses             : 0
% 0.20/0.46  #    Propositional clauses after purity: 0
% 0.20/0.46  #    Propositional unsat core size     : 0
% 0.20/0.46  #    Propositional preprocessing time  : 0.000
% 0.20/0.46  #    Propositional encoding time       : 0.000
% 0.20/0.46  #    Propositional solver time         : 0.000
% 0.20/0.46  #    Success case prop preproc time    : 0.000
% 0.20/0.46  #    Success case prop encoding time   : 0.000
% 0.20/0.46  #    Success case prop solver time     : 0.000
% 0.20/0.46  # Current number of processed clauses  : 78
% 0.20/0.46  #    Positive orientable unit clauses  : 13
% 0.20/0.46  #    Positive unorientable unit clauses: 0
% 0.20/0.46  #    Negative unit clauses             : 1
% 0.20/0.46  #    Non-unit-clauses                  : 64
% 0.20/0.46  # Current number of unprocessed clauses: 2419
% 0.20/0.46  # ...number of literals in the above   : 12554
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 151
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 3216
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 1439
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 100
% 0.20/0.46  # Unit Clause-clause subsumption calls : 100
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 25
% 0.20/0.46  # BW rewrite match successes           : 7
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 65840
% 0.20/0.46  
% 0.20/0.46  # -------------------------------------------------
% 0.20/0.46  # User time                : 0.109 s
% 0.20/0.46  # System time              : 0.006 s
% 0.20/0.46  # Total time               : 0.115 s
% 0.20/0.46  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
