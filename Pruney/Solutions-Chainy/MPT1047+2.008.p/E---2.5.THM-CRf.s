%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:12 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 588 expanded)
%              Number of clauses        :   50 ( 236 expanded)
%              Number of leaves         :   12 ( 157 expanded)
%              Depth                    :   13
%              Number of atoms          :  284 (1642 expanded)
%              Number of equality atoms :   85 ( 603 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
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

fof(l44_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t143_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => r1_partfun1(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

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

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,k1_tarski(X2))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
           => k5_partfun1(X1,k1_tarski(X2),X3) = k1_tarski(X4) ) ) ),
    inference(assume_negation,[status(cth)],[t164_funct_2])).

fof(c_0_13,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))
    & k5_partfun1(esk3_0,k1_tarski(esk4_0),esk5_0) != k1_tarski(esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_14,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X18,X19] :
      ( ( r2_hidden(esk2_2(X18,X19),X18)
        | X18 = k1_tarski(X19)
        | X18 = k1_xboole_0 )
      & ( esk2_2(X18,X19) != X19
        | X18 = k1_tarski(X19)
        | X18 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).

fof(c_0_17,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X9,X8)
        | X9 = X6
        | X9 = X7
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X6
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X7
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( esk1_3(X11,X12,X13) != X11
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( esk1_3(X11,X12,X13) != X12
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X13)
        | esk1_3(X11,X12,X13) = X11
        | esk1_3(X11,X12,X13) = X12
        | X13 = k2_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_18,plain,(
    ! [X23,X24,X25] :
      ( ( X24 = k1_xboole_0
        | v1_partfun1(X25,X23)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | ~ v1_funct_1(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( X23 != k1_xboole_0
        | v1_partfun1(X25,X23)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | ~ v1_funct_1(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).

cnf(c_0_19,negated_conjecture,
    ( k5_partfun1(esk3_0,k1_tarski(esk4_0),esk5_0) != k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_27,plain,(
    ! [X21,X22] :
      ( ~ r2_hidden(X21,X22)
      | ~ r1_tarski(X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_28,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_29,plain,(
    ! [X26,X27,X28,X29] :
      ( ~ v1_funct_1(X28)
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,k1_tarski(X27))))
      | ~ v1_funct_1(X29)
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,k1_tarski(X27))))
      | r1_partfun1(X28,X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_partfun1])])])).

cnf(c_0_30,negated_conjecture,
    ( k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0) != k1_enumset1(esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_enumset1(X2,X2,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_20]),c_0_21])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_20]),c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_20]),c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_40,plain,(
    ! [X38,X39,X40,X41] :
      ( ( v1_funct_1(X41)
        | ~ r2_hidden(X41,k5_partfun1(X38,X39,X40))
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( v1_funct_2(X41,X38,X39)
        | ~ r2_hidden(X41,k5_partfun1(X38,X39,X40))
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | ~ r2_hidden(X41,k5_partfun1(X38,X39,X40))
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).

cnf(c_0_41,negated_conjecture,
    ( k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0) = k1_xboole_0
    | r2_hidden(esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),X1),k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0))
    | k1_enumset1(X1,X1,X1) != k1_enumset1(esk6_0,esk6_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_43,plain,(
    ! [X30,X31,X32,X33] :
      ( ~ v1_funct_1(X32)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | ~ v1_funct_1(X33)
      | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | ~ v1_partfun1(X32,X30)
      | ~ v1_partfun1(X33,X30)
      | ~ r1_partfun1(X32,X33)
      | X32 = X33 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_partfun1])])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).

cnf(c_0_45,negated_conjecture,
    ( k1_enumset1(esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | v1_partfun1(esk6_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0) = k1_xboole_0
    | r2_hidden(esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk6_0),k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_20]),c_0_21])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( X1 = X4
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X4,X2)
    | ~ r1_partfun1(X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( v1_partfun1(esk6_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( r1_partfun1(X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_34]),c_0_36])])).

cnf(c_0_56,negated_conjecture,
    ( k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0) = k1_xboole_0
    | m1_subset_1(esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_57,negated_conjecture,
    ( k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0) = k1_xboole_0
    | v1_funct_1(esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_58,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_59,plain,(
    ! [X34,X35,X36,X37] :
      ( ( X35 = k1_xboole_0
        | r2_hidden(X37,k5_partfun1(X34,X35,X36))
        | ~ r1_partfun1(X36,X37)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X34,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ v1_funct_1(X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X34 != k1_xboole_0
        | r2_hidden(X37,k5_partfun1(X34,X35,X36))
        | ~ r1_partfun1(X36,X37)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X34,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ v1_funct_1(X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_2])])])])).

cnf(c_0_60,negated_conjecture,
    ( X1 = esk6_0
    | ~ r1_partfun1(X1,esk6_0)
    | ~ v1_partfun1(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_34]),c_0_54]),c_0_36])])).

cnf(c_0_61,negated_conjecture,
    ( k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0) = k1_xboole_0
    | r1_partfun1(esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0) = k1_xboole_0
    | v1_funct_2(esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk6_0),esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k5_partfun1(X3,X1,X4))
    | ~ r1_partfun1(X4,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk2_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_65,negated_conjecture,
    ( esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk6_0) = esk6_0
    | k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0) = k1_xboole_0
    | ~ v1_partfun1(esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk6_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_56]),c_0_57]),c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0) = k1_xboole_0
    | k1_enumset1(esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | v1_partfun1(esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk6_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_56]),c_0_57]),c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( k1_enumset1(esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | r2_hidden(X1,k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0))
    | ~ r1_partfun1(esk5_0,X1)
    | ~ v1_funct_2(X1,esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_50]),c_0_51])])).

cnf(c_0_68,negated_conjecture,
    ( r1_partfun1(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_50]),c_0_51])])).

cnf(c_0_69,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_enumset1(X2,X2,X2)
    | esk2_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_20]),c_0_21])).

cnf(c_0_70,negated_conjecture,
    ( esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk6_0) = esk6_0
    | k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0) = k1_xboole_0
    | k1_enumset1(esk4_0,esk4_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( k1_enumset1(esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk6_0,k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_34]),c_0_68]),c_0_35]),c_0_36])])).

cnf(c_0_72,negated_conjecture,
    ( k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0) = k1_xboole_0
    | k1_enumset1(esk4_0,esk4_0,esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_30])).

cnf(c_0_73,negated_conjecture,
    ( k1_enumset1(esk4_0,esk4_0,esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_46])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_73]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:28:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.15/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.15/0.40  #
% 0.15/0.40  # Preprocessing time       : 0.028 s
% 0.15/0.40  # Presaturation interreduction done
% 0.15/0.40  
% 0.15/0.40  # Proof found!
% 0.15/0.40  # SZS status Theorem
% 0.15/0.40  # SZS output start CNFRefutation
% 0.15/0.40  fof(t164_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>k5_partfun1(X1,k1_tarski(X2),X3)=k1_tarski(X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_2)).
% 0.15/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.15/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.15/0.40  fof(l44_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 0.15/0.40  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.15/0.40  fof(t132_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 0.15/0.40  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.15/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.15/0.40  fof(t143_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>r1_partfun1(X3,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_partfun1)).
% 0.15/0.40  fof(t158_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(r2_hidden(X4,k5_partfun1(X1,X2,X3))=>((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_2)).
% 0.15/0.40  fof(t148_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_partfun1(X3,X1)&v1_partfun1(X4,X1))&r1_partfun1(X3,X4))=>X3=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 0.15/0.40  fof(t155_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_hidden(X4,k5_partfun1(X1,X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_2)).
% 0.15/0.40  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>k5_partfun1(X1,k1_tarski(X2),X3)=k1_tarski(X4)))), inference(assume_negation,[status(cth)],[t164_funct_2])).
% 0.15/0.40  fof(c_0_13, negated_conjecture, ((v1_funct_1(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))))&k5_partfun1(esk3_0,k1_tarski(esk4_0),esk5_0)!=k1_tarski(esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.15/0.40  fof(c_0_14, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.15/0.40  fof(c_0_15, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.15/0.40  fof(c_0_16, plain, ![X18, X19]:((r2_hidden(esk2_2(X18,X19),X18)|(X18=k1_tarski(X19)|X18=k1_xboole_0))&(esk2_2(X18,X19)!=X19|(X18=k1_tarski(X19)|X18=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).
% 0.15/0.40  fof(c_0_17, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(X9=X6|X9=X7)|X8!=k2_tarski(X6,X7))&((X10!=X6|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))&(X10!=X7|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))))&(((esk1_3(X11,X12,X13)!=X11|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12))&(esk1_3(X11,X12,X13)!=X12|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(esk1_3(X11,X12,X13)=X11|esk1_3(X11,X12,X13)=X12)|X13=k2_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.15/0.40  fof(c_0_18, plain, ![X23, X24, X25]:((X24=k1_xboole_0|v1_partfun1(X25,X23)|(~v1_funct_1(X25)|~v1_funct_2(X25,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))|(~v1_funct_1(X25)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))&(X23!=k1_xboole_0|v1_partfun1(X25,X23)|(~v1_funct_1(X25)|~v1_funct_2(X25,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))|(~v1_funct_1(X25)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).
% 0.15/0.40  cnf(c_0_19, negated_conjecture, (k5_partfun1(esk3_0,k1_tarski(esk4_0),esk5_0)!=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.40  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.40  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.40  cnf(c_0_22, plain, (r2_hidden(esk2_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.40  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.40  cnf(c_0_24, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.40  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.40  cnf(c_0_26, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.40  fof(c_0_27, plain, ![X21, X22]:(~r2_hidden(X21,X22)|~r1_tarski(X22,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.15/0.40  fof(c_0_28, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.15/0.40  fof(c_0_29, plain, ![X26, X27, X28, X29]:(~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,k1_tarski(X27))))|(~v1_funct_1(X29)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,k1_tarski(X27))))|r1_partfun1(X28,X29))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_partfun1])])])).
% 0.15/0.40  cnf(c_0_30, negated_conjecture, (k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)!=k1_enumset1(esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_20]), c_0_21]), c_0_21])).
% 0.15/0.40  cnf(c_0_31, plain, (X1=k1_xboole_0|X1=k1_enumset1(X2,X2,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_20]), c_0_21])).
% 0.15/0.40  cnf(c_0_32, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X4)), inference(rw,[status(thm)],[c_0_23, c_0_21])).
% 0.15/0.40  cnf(c_0_33, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(cn,[status(thm)],[c_0_24])).
% 0.15/0.40  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_20]), c_0_21])).
% 0.15/0.40  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_20]), c_0_21])).
% 0.15/0.40  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.40  cnf(c_0_37, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.15/0.40  cnf(c_0_38, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.15/0.40  cnf(c_0_39, plain, (r1_partfun1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.15/0.40  fof(c_0_40, plain, ![X38, X39, X40, X41]:(((v1_funct_1(X41)|~r2_hidden(X41,k5_partfun1(X38,X39,X40))|(~v1_funct_1(X40)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))&(v1_funct_2(X41,X38,X39)|~r2_hidden(X41,k5_partfun1(X38,X39,X40))|(~v1_funct_1(X40)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))))&(m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|~r2_hidden(X41,k5_partfun1(X38,X39,X40))|(~v1_funct_1(X40)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).
% 0.15/0.40  cnf(c_0_41, negated_conjecture, (k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)=k1_xboole_0|r2_hidden(esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),X1),k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0))|k1_enumset1(X1,X1,X1)!=k1_enumset1(esk6_0,esk6_0,esk6_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.15/0.40  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.40  fof(c_0_43, plain, ![X30, X31, X32, X33]:(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|(~v1_partfun1(X32,X30)|~v1_partfun1(X33,X30)|~r1_partfun1(X32,X33)|X32=X33))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_partfun1])])])).
% 0.15/0.40  cnf(c_0_44, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).
% 0.15/0.40  cnf(c_0_45, negated_conjecture, (k1_enumset1(esk4_0,esk4_0,esk4_0)=k1_xboole_0|v1_partfun1(esk6_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])])).
% 0.15/0.40  cnf(c_0_46, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.15/0.40  cnf(c_0_47, plain, (r1_partfun1(X1,X4)|~v1_funct_1(X4)|~v1_funct_1(X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_20]), c_0_20]), c_0_21]), c_0_21])).
% 0.15/0.40  cnf(c_0_48, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.15/0.40  cnf(c_0_49, negated_conjecture, (k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)=k1_xboole_0|r2_hidden(esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk6_0),k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0))), inference(er,[status(thm)],[c_0_41])).
% 0.15/0.40  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_20]), c_0_21])).
% 0.15/0.40  cnf(c_0_51, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.40  cnf(c_0_52, plain, (v1_funct_1(X1)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.15/0.40  cnf(c_0_53, plain, (X1=X4|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_partfun1(X1,X2)|~v1_partfun1(X4,X2)|~r1_partfun1(X1,X4)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.15/0.40  cnf(c_0_54, negated_conjecture, (v1_partfun1(esk6_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.15/0.40  cnf(c_0_55, negated_conjecture, (r1_partfun1(X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_34]), c_0_36])])).
% 0.15/0.40  cnf(c_0_56, negated_conjecture, (k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)=k1_xboole_0|m1_subset_1(esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51])])).
% 0.15/0.40  cnf(c_0_57, negated_conjecture, (k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)=k1_xboole_0|v1_funct_1(esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_49]), c_0_50]), c_0_51])])).
% 0.15/0.40  cnf(c_0_58, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.15/0.40  fof(c_0_59, plain, ![X34, X35, X36, X37]:((X35=k1_xboole_0|r2_hidden(X37,k5_partfun1(X34,X35,X36))|~r1_partfun1(X36,X37)|(~v1_funct_1(X37)|~v1_funct_2(X37,X34,X35)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))|(~v1_funct_1(X36)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))&(X34!=k1_xboole_0|r2_hidden(X37,k5_partfun1(X34,X35,X36))|~r1_partfun1(X36,X37)|(~v1_funct_1(X37)|~v1_funct_2(X37,X34,X35)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))|(~v1_funct_1(X36)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_2])])])])).
% 0.15/0.40  cnf(c_0_60, negated_conjecture, (X1=esk6_0|~r1_partfun1(X1,esk6_0)|~v1_partfun1(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_34]), c_0_54]), c_0_36])])).
% 0.15/0.40  cnf(c_0_61, negated_conjecture, (k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)=k1_xboole_0|r1_partfun1(esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.15/0.40  cnf(c_0_62, negated_conjecture, (k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)=k1_xboole_0|v1_funct_2(esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk6_0),esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_49]), c_0_50]), c_0_51])])).
% 0.15/0.40  cnf(c_0_63, plain, (X1=k1_xboole_0|r2_hidden(X2,k5_partfun1(X3,X1,X4))|~r1_partfun1(X4,X2)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.15/0.40  cnf(c_0_64, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk2_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.40  cnf(c_0_65, negated_conjecture, (esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk6_0)=esk6_0|k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)=k1_xboole_0|~v1_partfun1(esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk6_0),esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_56]), c_0_57]), c_0_61])).
% 0.15/0.40  cnf(c_0_66, negated_conjecture, (k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)=k1_xboole_0|k1_enumset1(esk4_0,esk4_0,esk4_0)=k1_xboole_0|v1_partfun1(esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk6_0),esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_56]), c_0_57]), c_0_62])).
% 0.15/0.40  cnf(c_0_67, negated_conjecture, (k1_enumset1(esk4_0,esk4_0,esk4_0)=k1_xboole_0|r2_hidden(X1,k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0))|~r1_partfun1(esk5_0,X1)|~v1_funct_2(X1,esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_50]), c_0_51])])).
% 0.15/0.40  cnf(c_0_68, negated_conjecture, (r1_partfun1(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_50]), c_0_51])])).
% 0.15/0.40  cnf(c_0_69, plain, (X1=k1_xboole_0|X1=k1_enumset1(X2,X2,X2)|esk2_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_20]), c_0_21])).
% 0.15/0.40  cnf(c_0_70, negated_conjecture, (esk2_2(k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk6_0)=esk6_0|k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)=k1_xboole_0|k1_enumset1(esk4_0,esk4_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.15/0.40  cnf(c_0_71, negated_conjecture, (k1_enumset1(esk4_0,esk4_0,esk4_0)=k1_xboole_0|r2_hidden(esk6_0,k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_34]), c_0_68]), c_0_35]), c_0_36])])).
% 0.15/0.40  cnf(c_0_72, negated_conjecture, (k5_partfun1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)=k1_xboole_0|k1_enumset1(esk4_0,esk4_0,esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_30])).
% 0.15/0.40  cnf(c_0_73, negated_conjecture, (k1_enumset1(esk4_0,esk4_0,esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_46])).
% 0.15/0.40  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_73]), c_0_46]), ['proof']).
% 0.15/0.40  # SZS output end CNFRefutation
% 0.15/0.40  # Proof object total steps             : 75
% 0.15/0.40  # Proof object clause steps            : 50
% 0.15/0.40  # Proof object formula steps           : 25
% 0.15/0.40  # Proof object conjectures             : 32
% 0.15/0.40  # Proof object clause conjectures      : 29
% 0.15/0.40  # Proof object formula conjectures     : 3
% 0.15/0.40  # Proof object initial clauses used    : 20
% 0.15/0.40  # Proof object initial formulas used   : 12
% 0.15/0.40  # Proof object generating inferences   : 20
% 0.15/0.40  # Proof object simplifying inferences  : 56
% 0.15/0.40  # Training examples: 0 positive, 0 negative
% 0.15/0.40  # Parsed axioms                        : 12
% 0.15/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.40  # Initial clauses                      : 27
% 0.15/0.40  # Removed in clause preprocessing      : 2
% 0.15/0.40  # Initial clauses in saturation        : 25
% 0.15/0.40  # Processed clauses                    : 117
% 0.15/0.40  # ...of these trivial                  : 0
% 0.15/0.40  # ...subsumed                          : 12
% 0.15/0.40  # ...remaining for further processing  : 105
% 0.15/0.40  # Other redundant clauses eliminated   : 31
% 0.15/0.40  # Clauses deleted for lack of memory   : 0
% 0.15/0.40  # Backward-subsumed                    : 2
% 0.15/0.40  # Backward-rewritten                   : 29
% 0.15/0.40  # Generated clauses                    : 680
% 0.15/0.40  # ...of the previous two non-trivial   : 629
% 0.15/0.40  # Contextual simplify-reflections      : 8
% 0.15/0.40  # Paramodulations                      : 644
% 0.15/0.40  # Factorizations                       : 6
% 0.15/0.40  # Equation resolutions                 : 32
% 0.15/0.40  # Propositional unsat checks           : 0
% 0.15/0.40  #    Propositional check models        : 0
% 0.15/0.40  #    Propositional check unsatisfiable : 0
% 0.15/0.40  #    Propositional clauses             : 0
% 0.15/0.40  #    Propositional clauses after purity: 0
% 0.15/0.40  #    Propositional unsat core size     : 0
% 0.15/0.40  #    Propositional preprocessing time  : 0.000
% 0.15/0.40  #    Propositional encoding time       : 0.000
% 0.15/0.40  #    Propositional solver time         : 0.000
% 0.15/0.40  #    Success case prop preproc time    : 0.000
% 0.15/0.40  #    Success case prop encoding time   : 0.000
% 0.15/0.40  #    Success case prop solver time     : 0.000
% 0.15/0.40  # Current number of processed clauses  : 44
% 0.15/0.40  #    Positive orientable unit clauses  : 11
% 0.15/0.40  #    Positive unorientable unit clauses: 0
% 0.15/0.40  #    Negative unit clauses             : 1
% 0.15/0.40  #    Non-unit-clauses                  : 32
% 0.15/0.40  # Current number of unprocessed clauses: 538
% 0.15/0.40  # ...number of literals in the above   : 3087
% 0.15/0.40  # Current number of archived formulas  : 0
% 0.15/0.40  # Current number of archived clauses   : 58
% 0.15/0.40  # Clause-clause subsumption calls (NU) : 517
% 0.15/0.40  # Rec. Clause-clause subsumption calls : 134
% 0.15/0.40  # Non-unit clause-clause subsumptions  : 15
% 0.15/0.40  # Unit Clause-clause subsumption calls : 19
% 0.15/0.40  # Rewrite failures with RHS unbound    : 0
% 0.15/0.40  # BW rewrite match attempts            : 5
% 0.15/0.40  # BW rewrite match successes           : 3
% 0.15/0.40  # Condensation attempts                : 0
% 0.15/0.40  # Condensation successes               : 0
% 0.15/0.40  # Termbank termtop insertions          : 14980
% 0.15/0.40  
% 0.15/0.40  # -------------------------------------------------
% 0.15/0.40  # User time                : 0.048 s
% 0.15/0.40  # System time              : 0.005 s
% 0.15/0.40  # Total time               : 0.053 s
% 0.15/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
