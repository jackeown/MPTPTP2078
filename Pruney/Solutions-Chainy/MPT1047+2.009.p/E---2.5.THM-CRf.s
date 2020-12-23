%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:12 EST 2020

% Result     : Theorem 0.93s
% Output     : CNFRefutation 0.93s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 484 expanded)
%              Number of clauses        :   54 ( 186 expanded)
%              Number of leaves         :   15 ( 137 expanded)
%              Depth                    :   10
%              Number of atoms          :  384 (1201 expanded)
%              Number of equality atoms :  100 ( 489 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal clause size      :   68 (   3 average)
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

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(l44_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(t143_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => r1_partfun1(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

fof(t142_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(X4,k1_enumset1(X1,X2,X3))
    <=> ~ ( X4 != k1_xboole_0
          & X4 != k1_tarski(X1)
          & X4 != k1_tarski(X2)
          & X4 != k1_tarski(X3)
          & X4 != k2_tarski(X1,X2)
          & X4 != k2_tarski(X2,X3)
          & X4 != k2_tarski(X1,X3)
          & X4 != k1_enumset1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(t66_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,k1_tarski(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,k1_tarski(X2))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => r2_relset_1(X1,k1_tarski(X2),X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_2)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

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

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(d7_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( X4 = k5_partfun1(X1,X2,X3)
        <=> ! [X5] :
              ( r2_hidden(X5,X4)
            <=> ? [X6] :
                  ( v1_funct_1(X6)
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & X6 = X5
                  & v1_partfun1(X6,X1)
                  & r1_partfun1(X3,X6) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,k1_tarski(X2))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
           => k5_partfun1(X1,k1_tarski(X2),X3) = k1_tarski(X4) ) ) ),
    inference(assume_negation,[status(cth)],[t164_funct_2])).

fof(c_0_16,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0))))
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk5_0,k1_tarski(esk6_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0))))
    & k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0) != k1_tarski(esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_17,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X11,X12,X13] : k2_enumset1(X11,X11,X12,X13) = k1_enumset1(X11,X12,X13) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X14,X15] :
      ( ( r2_hidden(esk1_2(X14,X15),X14)
        | X14 = k1_tarski(X15)
        | X14 = k1_xboole_0 )
      & ( esk1_2(X14,X15) != X15
        | X14 = k1_tarski(X15)
        | X14 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).

fof(c_0_21,plain,(
    ! [X45,X46,X47,X48] :
      ( ~ v1_funct_1(X47)
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,k1_tarski(X46))))
      | ~ v1_funct_1(X48)
      | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,k1_tarski(X46))))
      | r1_partfun1(X47,X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_partfun1])])])).

fof(c_0_22,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ r1_tarski(X20,k1_enumset1(X17,X18,X19))
        | X20 = k1_xboole_0
        | X20 = k1_tarski(X17)
        | X20 = k1_tarski(X18)
        | X20 = k1_tarski(X19)
        | X20 = k2_tarski(X17,X18)
        | X20 = k2_tarski(X18,X19)
        | X20 = k2_tarski(X17,X19)
        | X20 = k1_enumset1(X17,X18,X19) )
      & ( X20 != k1_xboole_0
        | r1_tarski(X20,k1_enumset1(X17,X18,X19)) )
      & ( X20 != k1_tarski(X17)
        | r1_tarski(X20,k1_enumset1(X17,X18,X19)) )
      & ( X20 != k1_tarski(X18)
        | r1_tarski(X20,k1_enumset1(X17,X18,X19)) )
      & ( X20 != k1_tarski(X19)
        | r1_tarski(X20,k1_enumset1(X17,X18,X19)) )
      & ( X20 != k2_tarski(X17,X18)
        | r1_tarski(X20,k1_enumset1(X17,X18,X19)) )
      & ( X20 != k2_tarski(X18,X19)
        | r1_tarski(X20,k1_enumset1(X17,X18,X19)) )
      & ( X20 != k2_tarski(X17,X19)
        | r1_tarski(X20,k1_enumset1(X17,X18,X19)) )
      & ( X20 != k1_enumset1(X17,X18,X19)
        | r1_tarski(X20,k1_enumset1(X17,X18,X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).

fof(c_0_23,plain,(
    ! [X53,X54,X55,X56] :
      ( ~ v1_funct_1(X55)
      | ~ v1_funct_2(X55,X53,k1_tarski(X54))
      | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,k1_tarski(X54))))
      | ~ v1_funct_1(X56)
      | ~ v1_funct_2(X56,X53,k1_tarski(X54))
      | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X53,k1_tarski(X54))))
      | r2_relset_1(X53,k1_tarski(X54),X55,X56) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_funct_2])])])).

cnf(c_0_24,negated_conjecture,
    ( k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0) != k1_tarski(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_31,plain,(
    ! [X21,X22,X23] :
      ( ( r2_hidden(X21,X23)
        | ~ r1_tarski(k2_tarski(X21,X22),X23) )
      & ( r2_hidden(X22,X23)
        | ~ r1_tarski(k2_tarski(X21,X22),X23) )
      & ( ~ r2_hidden(X21,X23)
        | ~ r2_hidden(X22,X23)
        | r1_tarski(k2_tarski(X21,X22),X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k1_enumset1(X4,X2,X3))
    | X1 != k2_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_33,plain,(
    ! [X42,X43,X44] :
      ( ( X43 = k1_xboole_0
        | v1_partfun1(X44,X42)
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X42,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ v1_funct_1(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X42 != k1_xboole_0
        | v1_partfun1(X44,X42)
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X42,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ v1_funct_1(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).

fof(c_0_34,plain,(
    ! [X26,X27,X28,X29] :
      ( ( ~ r2_relset_1(X26,X27,X28,X29)
        | X28 = X29
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( X28 != X29
        | r2_relset_1(X26,X27,X28,X29)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_35,plain,
    ( r2_relset_1(X2,k1_tarski(X3),X1,X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,k1_tarski(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,k1_tarski(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) != k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_25]),c_0_26]),c_0_27])).

fof(c_0_38,plain,(
    ! [X30,X31,X32,X33,X34,X36,X37,X38,X40] :
      ( ( v1_funct_1(esk2_5(X30,X31,X32,X33,X34))
        | ~ r2_hidden(X34,X33)
        | X33 != k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( m1_subset_1(esk2_5(X30,X31,X32,X33,X34),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ r2_hidden(X34,X33)
        | X33 != k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( esk2_5(X30,X31,X32,X33,X34) = X34
        | ~ r2_hidden(X34,X33)
        | X33 != k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v1_partfun1(esk2_5(X30,X31,X32,X33,X34),X30)
        | ~ r2_hidden(X34,X33)
        | X33 != k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( r1_partfun1(X32,esk2_5(X30,X31,X32,X33,X34))
        | ~ r2_hidden(X34,X33)
        | X33 != k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( ~ v1_funct_1(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | X37 != X36
        | ~ v1_partfun1(X37,X30)
        | ~ r1_partfun1(X32,X37)
        | r2_hidden(X36,X33)
        | X33 != k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( ~ r2_hidden(esk3_4(X30,X31,X32,X38),X38)
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | X40 != esk3_4(X30,X31,X32,X38)
        | ~ v1_partfun1(X40,X30)
        | ~ r1_partfun1(X32,X40)
        | X38 = k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v1_funct_1(esk4_4(X30,X31,X32,X38))
        | r2_hidden(esk3_4(X30,X31,X32,X38),X38)
        | X38 = k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( m1_subset_1(esk4_4(X30,X31,X32,X38),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | r2_hidden(esk3_4(X30,X31,X32,X38),X38)
        | X38 = k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( esk4_4(X30,X31,X32,X38) = esk3_4(X30,X31,X32,X38)
        | r2_hidden(esk3_4(X30,X31,X32,X38),X38)
        | X38 = k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v1_partfun1(esk4_4(X30,X31,X32,X38),X30)
        | r2_hidden(esk3_4(X30,X31,X32,X38),X38)
        | X38 = k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( r1_partfun1(X32,esk4_4(X30,X31,X32,X38))
        | r2_hidden(esk3_4(X30,X31,X32,X38),X38)
        | X38 = k5_partfun1(X30,X31,X32)
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

cnf(c_0_39,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k2_enumset1(X4,X4,X2,X3))
    | X1 != k2_enumset1(X2,X2,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,k1_tarski(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_47,plain,(
    ! [X24,X25] :
      ( ~ r2_hidden(X24,X25)
      | ~ r1_tarski(X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_48,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_49,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,plain,
    ( r2_relset_1(X2,k2_enumset1(X3,X3,X3,X3),X1,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X2,k2_enumset1(X3,X3,X3,X3))
    | ~ v1_funct_2(X1,X2,k2_enumset1(X3,X3,X3,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_27]),c_0_27]),c_0_27])).

fof(c_0_51,plain,(
    ! [X49,X50,X51,X52] :
      ( ( v1_funct_1(X52)
        | ~ r2_hidden(X52,k5_partfun1(X49,X50,X51))
        | ~ v1_funct_1(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( v1_funct_2(X52,X49,X50)
        | ~ r2_hidden(X52,k5_partfun1(X49,X50,X51))
        | ~ v1_funct_1(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
        | ~ r2_hidden(X52,k5_partfun1(X49,X50,X51))
        | ~ v1_funct_1(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).

cnf(c_0_52,negated_conjecture,
    ( k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) = k1_xboole_0
    | r2_hidden(esk1_2(k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0),X1),k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))
    | k2_enumset1(X1,X1,X1,X1) != k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_53,plain,
    ( r2_hidden(X4,X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != X4
    | ~ v1_partfun1(X1,X2)
    | ~ r1_partfun1(X5,X1)
    | X6 != k5_partfun1(X2,X3,X5)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( r1_partfun1(X1,esk8_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_26]),c_0_27])).

cnf(c_0_58,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X1,X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_45])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_63,plain,
    ( X1 = X2
    | ~ v1_funct_2(X2,X3,k2_enumset1(X4,X4,X4,X4))
    | ~ v1_funct_2(X1,X3,k2_enumset1(X4,X4,X4,X4))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,k2_enumset1(X4,X4,X4,X4))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,k2_enumset1(X4,X4,X4,X4)))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_64,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,negated_conjecture,
    ( k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) = k1_xboole_0
    | r2_hidden(esk1_2(k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0),esk8_0),k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_67,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ r1_partfun1(X4,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).

cnf(c_0_69,negated_conjecture,
    ( r1_partfun1(esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X1,X3)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_71,negated_conjecture,
    ( k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) = k1_xboole_0
    | v1_partfun1(esk8_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_41]),c_0_40])])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_73,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk1_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_74,negated_conjecture,
    ( X1 = esk8_0
    | ~ v1_funct_2(X1,esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_60]),c_0_41]),c_0_40])])).

cnf(c_0_75,negated_conjecture,
    ( k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) = k1_xboole_0
    | v1_funct_2(esk1_2(k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0),esk8_0),esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_56]),c_0_55])])).

cnf(c_0_76,negated_conjecture,
    ( k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) = k1_xboole_0
    | m1_subset_1(esk1_2(k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0),esk8_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_65]),c_0_56]),c_0_55])])).

cnf(c_0_77,negated_conjecture,
    ( k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) = k1_xboole_0
    | v1_funct_1(esk1_2(k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0),esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_65]),c_0_56]),c_0_55])])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk8_0,k5_partfun1(X1,X2,esk7_0))
    | ~ v1_partfun1(esk8_0,X1)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_56]),c_0_41])])).

cnf(c_0_79,negated_conjecture,
    ( v1_partfun1(esk8_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_80,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | esk1_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_81,negated_conjecture,
    ( esk1_2(k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0),esk8_0) = esk8_0
    | k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk8_0,k5_partfun1(esk5_0,X1,esk7_0))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_36])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_55]),c_0_40])]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:16:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.93/1.12  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.93/1.12  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.93/1.12  #
% 0.93/1.12  # Preprocessing time       : 0.029 s
% 0.93/1.12  
% 0.93/1.12  # Proof found!
% 0.93/1.12  # SZS status Theorem
% 0.93/1.12  # SZS output start CNFRefutation
% 0.93/1.12  fof(t164_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>k5_partfun1(X1,k1_tarski(X2),X3)=k1_tarski(X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_2)).
% 0.93/1.12  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.93/1.12  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.93/1.12  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.93/1.12  fof(l44_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 0.93/1.12  fof(t143_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>r1_partfun1(X3,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_partfun1)).
% 0.93/1.12  fof(t142_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r1_tarski(X4,k1_enumset1(X1,X2,X3))<=>~((((((((X4!=k1_xboole_0&X4!=k1_tarski(X1))&X4!=k1_tarski(X2))&X4!=k1_tarski(X3))&X4!=k2_tarski(X1,X2))&X4!=k2_tarski(X2,X3))&X4!=k2_tarski(X1,X3))&X4!=k1_enumset1(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 0.93/1.12  fof(t66_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,k1_tarski(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>r2_relset_1(X1,k1_tarski(X2),X3,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_funct_2)).
% 0.93/1.12  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.93/1.12  fof(t132_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 0.93/1.12  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.93/1.12  fof(d7_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(X4=k5_partfun1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>?[X6]:((((v1_funct_1(X6)&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&X6=X5)&v1_partfun1(X6,X1))&r1_partfun1(X3,X6))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 0.93/1.12  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.93/1.12  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.93/1.12  fof(t158_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(r2_hidden(X4,k5_partfun1(X1,X2,X3))=>((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_2)).
% 0.93/1.12  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>k5_partfun1(X1,k1_tarski(X2),X3)=k1_tarski(X4)))), inference(assume_negation,[status(cth)],[t164_funct_2])).
% 0.93/1.12  fof(c_0_16, negated_conjecture, ((v1_funct_1(esk7_0)&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,k1_tarski(esk6_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))))&k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0)!=k1_tarski(esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.93/1.12  fof(c_0_17, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.93/1.12  fof(c_0_18, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.93/1.12  fof(c_0_19, plain, ![X11, X12, X13]:k2_enumset1(X11,X11,X12,X13)=k1_enumset1(X11,X12,X13), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.93/1.12  fof(c_0_20, plain, ![X14, X15]:((r2_hidden(esk1_2(X14,X15),X14)|(X14=k1_tarski(X15)|X14=k1_xboole_0))&(esk1_2(X14,X15)!=X15|(X14=k1_tarski(X15)|X14=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).
% 0.93/1.12  fof(c_0_21, plain, ![X45, X46, X47, X48]:(~v1_funct_1(X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,k1_tarski(X46))))|(~v1_funct_1(X48)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,k1_tarski(X46))))|r1_partfun1(X47,X48))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_partfun1])])])).
% 0.93/1.12  fof(c_0_22, plain, ![X17, X18, X19, X20]:((~r1_tarski(X20,k1_enumset1(X17,X18,X19))|(X20=k1_xboole_0|X20=k1_tarski(X17)|X20=k1_tarski(X18)|X20=k1_tarski(X19)|X20=k2_tarski(X17,X18)|X20=k2_tarski(X18,X19)|X20=k2_tarski(X17,X19)|X20=k1_enumset1(X17,X18,X19)))&((((((((X20!=k1_xboole_0|r1_tarski(X20,k1_enumset1(X17,X18,X19)))&(X20!=k1_tarski(X17)|r1_tarski(X20,k1_enumset1(X17,X18,X19))))&(X20!=k1_tarski(X18)|r1_tarski(X20,k1_enumset1(X17,X18,X19))))&(X20!=k1_tarski(X19)|r1_tarski(X20,k1_enumset1(X17,X18,X19))))&(X20!=k2_tarski(X17,X18)|r1_tarski(X20,k1_enumset1(X17,X18,X19))))&(X20!=k2_tarski(X18,X19)|r1_tarski(X20,k1_enumset1(X17,X18,X19))))&(X20!=k2_tarski(X17,X19)|r1_tarski(X20,k1_enumset1(X17,X18,X19))))&(X20!=k1_enumset1(X17,X18,X19)|r1_tarski(X20,k1_enumset1(X17,X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).
% 0.93/1.12  fof(c_0_23, plain, ![X53, X54, X55, X56]:(~v1_funct_1(X55)|~v1_funct_2(X55,X53,k1_tarski(X54))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,k1_tarski(X54))))|(~v1_funct_1(X56)|~v1_funct_2(X56,X53,k1_tarski(X54))|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X53,k1_tarski(X54))))|r2_relset_1(X53,k1_tarski(X54),X55,X56))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_funct_2])])])).
% 0.93/1.12  cnf(c_0_24, negated_conjecture, (k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0)!=k1_tarski(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.93/1.12  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.93/1.12  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.93/1.12  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.93/1.12  cnf(c_0_28, plain, (r2_hidden(esk1_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.93/1.12  cnf(c_0_29, plain, (r1_partfun1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.93/1.12  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.93/1.12  fof(c_0_31, plain, ![X21, X22, X23]:(((r2_hidden(X21,X23)|~r1_tarski(k2_tarski(X21,X22),X23))&(r2_hidden(X22,X23)|~r1_tarski(k2_tarski(X21,X22),X23)))&(~r2_hidden(X21,X23)|~r2_hidden(X22,X23)|r1_tarski(k2_tarski(X21,X22),X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.93/1.12  cnf(c_0_32, plain, (r1_tarski(X1,k1_enumset1(X4,X2,X3))|X1!=k2_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.93/1.12  fof(c_0_33, plain, ![X42, X43, X44]:((X43=k1_xboole_0|v1_partfun1(X44,X42)|(~v1_funct_1(X44)|~v1_funct_2(X44,X42,X43)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))|(~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))&(X42!=k1_xboole_0|v1_partfun1(X44,X42)|(~v1_funct_1(X44)|~v1_funct_2(X44,X42,X43)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))|(~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).
% 0.93/1.12  fof(c_0_34, plain, ![X26, X27, X28, X29]:((~r2_relset_1(X26,X27,X28,X29)|X28=X29|(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))&(X28!=X29|r2_relset_1(X26,X27,X28,X29)|(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.93/1.12  cnf(c_0_35, plain, (r2_relset_1(X2,k1_tarski(X3),X1,X4)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,k1_tarski(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,k1_tarski(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.93/1.12  cnf(c_0_36, negated_conjecture, (k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)!=k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27])).
% 0.93/1.12  cnf(c_0_37, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|r2_hidden(esk1_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_25]), c_0_26]), c_0_27])).
% 0.93/1.12  fof(c_0_38, plain, ![X30, X31, X32, X33, X34, X36, X37, X38, X40]:(((((((v1_funct_1(esk2_5(X30,X31,X32,X33,X34))|~r2_hidden(X34,X33)|X33!=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&(m1_subset_1(esk2_5(X30,X31,X32,X33,X34),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|~r2_hidden(X34,X33)|X33!=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&(esk2_5(X30,X31,X32,X33,X34)=X34|~r2_hidden(X34,X33)|X33!=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&(v1_partfun1(esk2_5(X30,X31,X32,X33,X34),X30)|~r2_hidden(X34,X33)|X33!=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&(r1_partfun1(X32,esk2_5(X30,X31,X32,X33,X34))|~r2_hidden(X34,X33)|X33!=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&(~v1_funct_1(X37)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|X37!=X36|~v1_partfun1(X37,X30)|~r1_partfun1(X32,X37)|r2_hidden(X36,X33)|X33!=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&((~r2_hidden(esk3_4(X30,X31,X32,X38),X38)|(~v1_funct_1(X40)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|X40!=esk3_4(X30,X31,X32,X38)|~v1_partfun1(X40,X30)|~r1_partfun1(X32,X40))|X38=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&(((((v1_funct_1(esk4_4(X30,X31,X32,X38))|r2_hidden(esk3_4(X30,X31,X32,X38),X38)|X38=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&(m1_subset_1(esk4_4(X30,X31,X32,X38),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|r2_hidden(esk3_4(X30,X31,X32,X38),X38)|X38=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&(esk4_4(X30,X31,X32,X38)=esk3_4(X30,X31,X32,X38)|r2_hidden(esk3_4(X30,X31,X32,X38),X38)|X38=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&(v1_partfun1(esk4_4(X30,X31,X32,X38),X30)|r2_hidden(esk3_4(X30,X31,X32,X38),X38)|X38=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&(r1_partfun1(X32,esk4_4(X30,X31,X32,X38))|r2_hidden(esk3_4(X30,X31,X32,X38),X38)|X38=k5_partfun1(X30,X31,X32)|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).
% 0.93/1.12  cnf(c_0_39, plain, (r1_partfun1(X1,X4)|~v1_funct_1(X4)|~v1_funct_1(X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27])).
% 0.93/1.12  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_25]), c_0_26]), c_0_27])).
% 0.93/1.12  cnf(c_0_41, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.93/1.12  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.93/1.12  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.93/1.12  cnf(c_0_44, plain, (r1_tarski(X1,k2_enumset1(X4,X4,X2,X3))|X1!=k2_enumset1(X2,X2,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_26]), c_0_27]), c_0_27])).
% 0.93/1.12  cnf(c_0_45, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.93/1.12  cnf(c_0_46, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,k1_tarski(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.93/1.12  fof(c_0_47, plain, ![X24, X25]:(~r2_hidden(X24,X25)|~r1_tarski(X25,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.93/1.12  fof(c_0_48, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.93/1.12  cnf(c_0_49, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.93/1.12  cnf(c_0_50, plain, (r2_relset_1(X2,k2_enumset1(X3,X3,X3,X3),X1,X4)|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X2,k2_enumset1(X3,X3,X3,X3))|~v1_funct_2(X1,X2,k2_enumset1(X3,X3,X3,X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_27]), c_0_27]), c_0_27])).
% 0.93/1.12  fof(c_0_51, plain, ![X49, X50, X51, X52]:(((v1_funct_1(X52)|~r2_hidden(X52,k5_partfun1(X49,X50,X51))|(~v1_funct_1(X51)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))))&(v1_funct_2(X52,X49,X50)|~r2_hidden(X52,k5_partfun1(X49,X50,X51))|(~v1_funct_1(X51)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))))&(m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|~r2_hidden(X52,k5_partfun1(X49,X50,X51))|(~v1_funct_1(X51)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).
% 0.93/1.12  cnf(c_0_52, negated_conjecture, (k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)=k1_xboole_0|r2_hidden(esk1_2(k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0),X1),k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))|k2_enumset1(X1,X1,X1,X1)!=k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.93/1.12  cnf(c_0_53, plain, (r2_hidden(X4,X6)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X1!=X4|~v1_partfun1(X1,X2)|~r1_partfun1(X5,X1)|X6!=k5_partfun1(X2,X3,X5)|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.93/1.12  cnf(c_0_54, negated_conjecture, (r1_partfun1(X1,esk8_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.93/1.12  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_25]), c_0_26]), c_0_27])).
% 0.93/1.12  cnf(c_0_56, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.93/1.12  cnf(c_0_57, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_26]), c_0_27])).
% 0.93/1.12  cnf(c_0_58, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X1,X2))), inference(er,[status(thm)],[c_0_44])).
% 0.93/1.12  cnf(c_0_59, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(cn,[status(thm)],[c_0_45])).
% 0.93/1.12  cnf(c_0_60, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_25]), c_0_26]), c_0_27])).
% 0.93/1.12  cnf(c_0_61, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.93/1.12  cnf(c_0_62, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.93/1.12  cnf(c_0_63, plain, (X1=X2|~v1_funct_2(X2,X3,k2_enumset1(X4,X4,X4,X4))|~v1_funct_2(X1,X3,k2_enumset1(X4,X4,X4,X4))|~v1_funct_1(X2)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,k2_enumset1(X4,X4,X4,X4))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,k2_enumset1(X4,X4,X4,X4))))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.93/1.12  cnf(c_0_64, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.93/1.12  cnf(c_0_65, negated_conjecture, (k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)=k1_xboole_0|r2_hidden(esk1_2(k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0),esk8_0),k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))), inference(er,[status(thm)],[c_0_52])).
% 0.93/1.12  cnf(c_0_66, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.93/1.12  cnf(c_0_67, plain, (v1_funct_1(X1)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.93/1.12  cnf(c_0_68, plain, (r2_hidden(X1,k5_partfun1(X2,X3,X4))|~r1_partfun1(X4,X1)|~v1_partfun1(X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).
% 0.93/1.12  cnf(c_0_69, negated_conjecture, (r1_partfun1(esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.93/1.12  cnf(c_0_70, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X1,X3))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.93/1.12  cnf(c_0_71, negated_conjecture, (k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)=k1_xboole_0|v1_partfun1(esk8_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_41]), c_0_40])])).
% 0.93/1.12  cnf(c_0_72, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.93/1.12  cnf(c_0_73, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk1_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.93/1.12  cnf(c_0_74, negated_conjecture, (X1=esk8_0|~v1_funct_2(X1,esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_60]), c_0_41]), c_0_40])])).
% 0.93/1.12  cnf(c_0_75, negated_conjecture, (k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)=k1_xboole_0|v1_funct_2(esk1_2(k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0),esk8_0),esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_56]), c_0_55])])).
% 0.93/1.12  cnf(c_0_76, negated_conjecture, (k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)=k1_xboole_0|m1_subset_1(esk1_2(k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0),esk8_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_65]), c_0_56]), c_0_55])])).
% 0.93/1.12  cnf(c_0_77, negated_conjecture, (k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)=k1_xboole_0|v1_funct_1(esk1_2(k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0),esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_65]), c_0_56]), c_0_55])])).
% 0.93/1.12  cnf(c_0_78, negated_conjecture, (r2_hidden(esk8_0,k5_partfun1(X1,X2,esk7_0))|~v1_partfun1(esk8_0,X1)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_56]), c_0_41])])).
% 0.93/1.12  cnf(c_0_79, negated_conjecture, (v1_partfun1(esk8_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])).
% 0.93/1.12  cnf(c_0_80, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|esk1_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_25]), c_0_26]), c_0_27])).
% 0.93/1.12  cnf(c_0_81, negated_conjecture, (esk1_2(k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0),esk8_0)=esk8_0|k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76]), c_0_77])).
% 0.93/1.12  cnf(c_0_82, negated_conjecture, (r2_hidden(esk8_0,k5_partfun1(esk5_0,X1,esk7_0))|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.93/1.12  cnf(c_0_83, negated_conjecture, (k5_partfun1(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_36])).
% 0.93/1.12  cnf(c_0_84, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_55]), c_0_40])]), c_0_72]), ['proof']).
% 0.93/1.12  # SZS output end CNFRefutation
% 0.93/1.12  # Proof object total steps             : 85
% 0.93/1.12  # Proof object clause steps            : 54
% 0.93/1.12  # Proof object formula steps           : 31
% 0.93/1.12  # Proof object conjectures             : 28
% 0.93/1.12  # Proof object clause conjectures      : 25
% 0.93/1.12  # Proof object formula conjectures     : 3
% 0.93/1.12  # Proof object initial clauses used    : 23
% 0.93/1.12  # Proof object initial formulas used   : 15
% 0.93/1.12  # Proof object generating inferences   : 18
% 0.93/1.12  # Proof object simplifying inferences  : 81
% 0.93/1.12  # Training examples: 0 positive, 0 negative
% 0.93/1.12  # Parsed axioms                        : 15
% 0.93/1.12  # Removed by relevancy pruning/SinE    : 0
% 0.93/1.12  # Initial clauses                      : 46
% 0.93/1.12  # Removed in clause preprocessing      : 3
% 0.93/1.12  # Initial clauses in saturation        : 43
% 0.93/1.12  # Processed clauses                    : 991
% 0.93/1.12  # ...of these trivial                  : 0
% 0.93/1.12  # ...subsumed                          : 525
% 0.93/1.12  # ...remaining for further processing  : 466
% 0.93/1.12  # Other redundant clauses eliminated   : 96
% 0.93/1.12  # Clauses deleted for lack of memory   : 0
% 0.93/1.12  # Backward-subsumed                    : 18
% 0.93/1.12  # Backward-rewritten                   : 46
% 0.93/1.12  # Generated clauses                    : 32957
% 0.93/1.12  # ...of the previous two non-trivial   : 32616
% 0.93/1.12  # Contextual simplify-reflections      : 13
% 0.93/1.12  # Paramodulations                      : 32734
% 0.93/1.12  # Factorizations                       : 126
% 0.93/1.12  # Equation resolutions                 : 98
% 0.93/1.12  # Propositional unsat checks           : 0
% 0.93/1.12  #    Propositional check models        : 0
% 0.93/1.12  #    Propositional check unsatisfiable : 0
% 0.93/1.12  #    Propositional clauses             : 0
% 0.93/1.12  #    Propositional clauses after purity: 0
% 0.93/1.12  #    Propositional unsat core size     : 0
% 0.93/1.12  #    Propositional preprocessing time  : 0.000
% 0.93/1.12  #    Propositional encoding time       : 0.000
% 0.93/1.12  #    Propositional solver time         : 0.000
% 0.93/1.12  #    Success case prop preproc time    : 0.000
% 0.93/1.12  #    Success case prop encoding time   : 0.000
% 0.93/1.12  #    Success case prop solver time     : 0.000
% 0.93/1.12  # Current number of processed clauses  : 385
% 0.93/1.12  #    Positive orientable unit clauses  : 22
% 0.93/1.12  #    Positive unorientable unit clauses: 0
% 0.93/1.12  #    Negative unit clauses             : 8
% 0.93/1.12  #    Non-unit-clauses                  : 355
% 0.93/1.12  # Current number of unprocessed clauses: 31587
% 0.93/1.12  # ...number of literals in the above   : 253968
% 0.93/1.12  # Current number of archived formulas  : 0
% 0.93/1.12  # Current number of archived clauses   : 67
% 0.93/1.12  # Clause-clause subsumption calls (NU) : 30244
% 0.93/1.12  # Rec. Clause-clause subsumption calls : 6545
% 0.93/1.12  # Non-unit clause-clause subsumptions  : 538
% 0.93/1.12  # Unit Clause-clause subsumption calls : 269
% 0.93/1.12  # Rewrite failures with RHS unbound    : 0
% 0.93/1.12  # BW rewrite match attempts            : 39
% 0.93/1.12  # BW rewrite match successes           : 2
% 0.93/1.12  # Condensation attempts                : 0
% 0.93/1.12  # Condensation successes               : 0
% 0.93/1.12  # Termbank termtop insertions          : 830221
% 0.93/1.12  
% 0.93/1.12  # -------------------------------------------------
% 0.93/1.12  # User time                : 0.750 s
% 0.93/1.12  # System time              : 0.028 s
% 0.93/1.12  # Total time               : 0.779 s
% 0.93/1.12  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
