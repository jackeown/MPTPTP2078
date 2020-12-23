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
% DateTime   : Thu Dec  3 11:07:06 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 312 expanded)
%              Number of clauses        :   54 ( 139 expanded)
%              Number of leaves         :   11 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  287 (1598 expanded)
%              Number of equality atoms :   67 ( 329 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t155_funct_2,conjecture,(
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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

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

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(c_0_11,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
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
    inference(assume_negation,[status(cth)],[t155_funct_2])).

fof(c_0_13,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk5_0,esk6_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & r1_partfun1(esk7_0,esk8_0)
    & ( esk6_0 != k1_xboole_0
      | esk5_0 = k1_xboole_0 )
    & ~ r2_hidden(esk8_0,k5_partfun1(esk5_0,esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_16,plain,(
    ! [X15,X16] :
      ( ( k2_zfmisc_1(X15,X16) != k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_17,plain,(
    ! [X23,X24,X25] :
      ( ~ r2_hidden(X23,X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X25))
      | ~ v1_xboole_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X32,X33,X34,X35,X36,X38,X39,X40,X42] :
      ( ( v1_funct_1(esk2_5(X32,X33,X34,X35,X36))
        | ~ r2_hidden(X36,X35)
        | X35 != k5_partfun1(X32,X33,X34)
        | ~ v1_funct_1(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( m1_subset_1(esk2_5(X32,X33,X34,X35,X36),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | ~ r2_hidden(X36,X35)
        | X35 != k5_partfun1(X32,X33,X34)
        | ~ v1_funct_1(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( esk2_5(X32,X33,X34,X35,X36) = X36
        | ~ r2_hidden(X36,X35)
        | X35 != k5_partfun1(X32,X33,X34)
        | ~ v1_funct_1(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( v1_partfun1(esk2_5(X32,X33,X34,X35,X36),X32)
        | ~ r2_hidden(X36,X35)
        | X35 != k5_partfun1(X32,X33,X34)
        | ~ v1_funct_1(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( r1_partfun1(X34,esk2_5(X32,X33,X34,X35,X36))
        | ~ r2_hidden(X36,X35)
        | X35 != k5_partfun1(X32,X33,X34)
        | ~ v1_funct_1(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( ~ v1_funct_1(X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | X39 != X38
        | ~ v1_partfun1(X39,X32)
        | ~ r1_partfun1(X34,X39)
        | r2_hidden(X38,X35)
        | X35 != k5_partfun1(X32,X33,X34)
        | ~ v1_funct_1(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( ~ r2_hidden(esk3_4(X32,X33,X34,X40),X40)
        | ~ v1_funct_1(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | X42 != esk3_4(X32,X33,X34,X40)
        | ~ v1_partfun1(X42,X32)
        | ~ r1_partfun1(X34,X42)
        | X40 = k5_partfun1(X32,X33,X34)
        | ~ v1_funct_1(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( v1_funct_1(esk4_4(X32,X33,X34,X40))
        | r2_hidden(esk3_4(X32,X33,X34,X40),X40)
        | X40 = k5_partfun1(X32,X33,X34)
        | ~ v1_funct_1(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( m1_subset_1(esk4_4(X32,X33,X34,X40),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | r2_hidden(esk3_4(X32,X33,X34,X40),X40)
        | X40 = k5_partfun1(X32,X33,X34)
        | ~ v1_funct_1(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( esk4_4(X32,X33,X34,X40) = esk3_4(X32,X33,X34,X40)
        | r2_hidden(esk3_4(X32,X33,X34,X40),X40)
        | X40 = k5_partfun1(X32,X33,X34)
        | ~ v1_funct_1(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( v1_partfun1(esk4_4(X32,X33,X34,X40),X32)
        | r2_hidden(esk3_4(X32,X33,X34,X40),X40)
        | X40 = k5_partfun1(X32,X33,X34)
        | ~ v1_funct_1(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( r1_partfun1(X34,esk4_4(X32,X33,X34,X40))
        | r2_hidden(esk3_4(X32,X33,X34,X40),X40)
        | X40 = k5_partfun1(X32,X33,X34)
        | ~ v1_funct_1(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X17)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_26,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_27,plain,(
    ! [X29,X30,X31] :
      ( ( v1_funct_1(X31)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | v1_xboole_0(X30) )
      & ( v1_partfun1(X31,X29)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | v1_xboole_0(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_28,plain,
    ( r2_hidden(X4,X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != X4
    | ~ v1_partfun1(X1,X2)
    | ~ r1_partfun1(X5,X1)
    | X6 != k5_partfun1(X2,X3,X5)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0))
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | X2 != k5_partfun1(X3,X4,X5)
    | ~ r1_partfun1(X5,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X3)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_29]),c_0_30])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k1_xboole_0))
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_22])).

cnf(c_0_42,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_32])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( v1_partfun1(esk8_0,esk5_0)
    | v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_31])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k5_partfun1(esk5_0,esk6_0,esk7_0)
    | ~ r1_partfun1(esk7_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_21]),c_0_39])])).

cnf(c_0_46,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_41]),c_0_30])])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_34])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,negated_conjecture,
    ( v1_partfun1(esk8_0,esk5_0)
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k5_partfun1(esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk5_0,esk6_0,esk7_0))
    | ~ r1_partfun1(esk7_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( r1_partfun1(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_55,negated_conjecture,
    ( X1 = esk7_0
    | esk6_0 != k1_xboole_0
    | ~ r1_tarski(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk8_0,X1)
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_34])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_30])).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( v1_partfun1(esk8_0,esk5_0)
    | m1_subset_1(esk6_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_partfun1(esk8_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_37]),c_0_31])])).

cnf(c_0_61,negated_conjecture,
    ( esk7_0 = esk8_0
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_57])).

cnf(c_0_63,plain,
    ( k1_xboole_0 = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_65,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_xboole_0(X26)
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | v1_partfun1(X28,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

cnf(c_0_66,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_70,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_71,plain,
    ( v1_partfun1(k1_xboole_0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_32])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_partfun1(k1_xboole_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_67])])).

cnf(c_0_74,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_30])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73]),c_0_74])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:36:46 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.18/0.38  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_S0Y
% 0.18/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.38  #
% 0.18/0.38  # Preprocessing time       : 0.025 s
% 0.18/0.38  
% 0.18/0.38  # Proof found!
% 0.18/0.38  # SZS status Theorem
% 0.18/0.38  # SZS output start CNFRefutation
% 0.18/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.38  fof(t155_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_hidden(X4,k5_partfun1(X1,X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_2)).
% 0.18/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.18/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.18/0.38  fof(d7_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(X4=k5_partfun1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>?[X6]:((((v1_funct_1(X6)&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&X6=X5)&v1_partfun1(X6,X1))&r1_partfun1(X3,X6))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 0.18/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.18/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.18/0.38  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.18/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.18/0.38  fof(cc1_partfun1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_partfun1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 0.18/0.38  fof(c_0_11, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.38  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_hidden(X4,k5_partfun1(X1,X2,X3))))))), inference(assume_negation,[status(cth)],[t155_funct_2])).
% 0.18/0.38  fof(c_0_13, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.38  cnf(c_0_14, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.38  fof(c_0_15, negated_conjecture, ((v1_funct_1(esk7_0)&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(r1_partfun1(esk7_0,esk8_0)&((esk6_0!=k1_xboole_0|esk5_0=k1_xboole_0)&~r2_hidden(esk8_0,k5_partfun1(esk5_0,esk6_0,esk7_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.18/0.38  fof(c_0_16, plain, ![X15, X16]:((k2_zfmisc_1(X15,X16)!=k1_xboole_0|(X15=k1_xboole_0|X16=k1_xboole_0))&((X15!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0)&(X16!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.18/0.38  fof(c_0_17, plain, ![X23, X24, X25]:(~r2_hidden(X23,X24)|~m1_subset_1(X24,k1_zfmisc_1(X25))|~v1_xboole_0(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.18/0.38  cnf(c_0_18, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.38  cnf(c_0_19, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_14])).
% 0.18/0.38  fof(c_0_20, plain, ![X32, X33, X34, X35, X36, X38, X39, X40, X42]:(((((((v1_funct_1(esk2_5(X32,X33,X34,X35,X36))|~r2_hidden(X36,X35)|X35!=k5_partfun1(X32,X33,X34)|(~v1_funct_1(X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&(m1_subset_1(esk2_5(X32,X33,X34,X35,X36),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|~r2_hidden(X36,X35)|X35!=k5_partfun1(X32,X33,X34)|(~v1_funct_1(X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))&(esk2_5(X32,X33,X34,X35,X36)=X36|~r2_hidden(X36,X35)|X35!=k5_partfun1(X32,X33,X34)|(~v1_funct_1(X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))&(v1_partfun1(esk2_5(X32,X33,X34,X35,X36),X32)|~r2_hidden(X36,X35)|X35!=k5_partfun1(X32,X33,X34)|(~v1_funct_1(X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))&(r1_partfun1(X34,esk2_5(X32,X33,X34,X35,X36))|~r2_hidden(X36,X35)|X35!=k5_partfun1(X32,X33,X34)|(~v1_funct_1(X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))&(~v1_funct_1(X39)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|X39!=X38|~v1_partfun1(X39,X32)|~r1_partfun1(X34,X39)|r2_hidden(X38,X35)|X35!=k5_partfun1(X32,X33,X34)|(~v1_funct_1(X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))&((~r2_hidden(esk3_4(X32,X33,X34,X40),X40)|(~v1_funct_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|X42!=esk3_4(X32,X33,X34,X40)|~v1_partfun1(X42,X32)|~r1_partfun1(X34,X42))|X40=k5_partfun1(X32,X33,X34)|(~v1_funct_1(X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&(((((v1_funct_1(esk4_4(X32,X33,X34,X40))|r2_hidden(esk3_4(X32,X33,X34,X40),X40)|X40=k5_partfun1(X32,X33,X34)|(~v1_funct_1(X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&(m1_subset_1(esk4_4(X32,X33,X34,X40),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|r2_hidden(esk3_4(X32,X33,X34,X40),X40)|X40=k5_partfun1(X32,X33,X34)|(~v1_funct_1(X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))&(esk4_4(X32,X33,X34,X40)=esk3_4(X32,X33,X34,X40)|r2_hidden(esk3_4(X32,X33,X34,X40),X40)|X40=k5_partfun1(X32,X33,X34)|(~v1_funct_1(X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))&(v1_partfun1(esk4_4(X32,X33,X34,X40),X32)|r2_hidden(esk3_4(X32,X33,X34,X40),X40)|X40=k5_partfun1(X32,X33,X34)|(~v1_funct_1(X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))&(r1_partfun1(X34,esk4_4(X32,X33,X34,X40))|r2_hidden(esk3_4(X32,X33,X34,X40),X40)|X40=k5_partfun1(X32,X33,X34)|(~v1_funct_1(X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).
% 0.18/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_22, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.38  fof(c_0_23, plain, ![X17]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X17)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.18/0.38  cnf(c_0_24, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.38  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.38  fof(c_0_26, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.18/0.38  fof(c_0_27, plain, ![X29, X30, X31]:((v1_funct_1(X31)|(~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|v1_xboole_0(X30))&(v1_partfun1(X31,X29)|(~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|v1_xboole_0(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.18/0.38  cnf(c_0_28, plain, (r2_hidden(X4,X6)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X1!=X4|~v1_partfun1(X1,X2)|~r1_partfun1(X5,X1)|X6!=k5_partfun1(X2,X3,X5)|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.38  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0))|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.18/0.38  cnf(c_0_30, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.18/0.38  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_32, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.38  cnf(c_0_33, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.38  cnf(c_0_34, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.38  cnf(c_0_35, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.38  cnf(c_0_36, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_38, plain, (r2_hidden(X1,X2)|X2!=k5_partfun1(X3,X4,X5)|~r1_partfun1(X5,X1)|~v1_funct_1(X5)|~v1_funct_1(X1)|~v1_partfun1(X1,X3)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(er,[status(thm)],[c_0_28])).
% 0.18/0.38  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_40, negated_conjecture, (esk6_0!=k1_xboole_0|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_29]), c_0_30])])).
% 0.18/0.38  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k1_xboole_0))|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_22])).
% 0.18/0.38  cnf(c_0_42, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_32])).
% 0.18/0.38  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.38  cnf(c_0_44, negated_conjecture, (v1_partfun1(esk8_0,esk5_0)|v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_31])])).
% 0.18/0.38  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,X2)|X2!=k5_partfun1(esk5_0,esk6_0,esk7_0)|~r1_partfun1(esk7_0,X1)|~v1_funct_1(X1)|~v1_partfun1(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_21]), c_0_39])])).
% 0.18/0.38  cnf(c_0_46, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.38  cnf(c_0_47, negated_conjecture, (r1_tarski(esk7_0,X1)|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_34])).
% 0.18/0.38  cnf(c_0_48, negated_conjecture, (esk6_0!=k1_xboole_0|~r2_hidden(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_41]), c_0_30])])).
% 0.18/0.38  cnf(c_0_49, plain, (r1_tarski(k1_xboole_0,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_42, c_0_34])).
% 0.18/0.38  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.38  cnf(c_0_51, negated_conjecture, (v1_partfun1(esk8_0,esk5_0)|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.18/0.38  cnf(c_0_52, negated_conjecture, (~r2_hidden(esk8_0,k5_partfun1(esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_53, negated_conjecture, (r2_hidden(X1,k5_partfun1(esk5_0,esk6_0,esk7_0))|~r1_partfun1(esk7_0,X1)|~v1_funct_1(X1)|~v1_partfun1(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(er,[status(thm)],[c_0_45])).
% 0.18/0.38  cnf(c_0_54, negated_conjecture, (r1_partfun1(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_55, negated_conjecture, (X1=esk7_0|esk6_0!=k1_xboole_0|~r1_tarski(X1,esk7_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.18/0.38  cnf(c_0_56, negated_conjecture, (r1_tarski(esk8_0,X1)|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_34])).
% 0.18/0.38  cnf(c_0_57, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_49, c_0_30])).
% 0.18/0.38  cnf(c_0_58, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_46, c_0_50])).
% 0.18/0.38  cnf(c_0_59, negated_conjecture, (v1_partfun1(esk8_0,esk5_0)|m1_subset_1(esk6_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_18, c_0_51])).
% 0.18/0.38  cnf(c_0_60, negated_conjecture, (~v1_partfun1(esk8_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_37]), c_0_31])])).
% 0.18/0.38  cnf(c_0_61, negated_conjecture, (esk7_0=esk8_0|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.18/0.38  cnf(c_0_62, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_57])).
% 0.18/0.38  cnf(c_0_63, plain, (k1_xboole_0=X1|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_58, c_0_57])).
% 0.18/0.38  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[c_0_59, c_0_60])).
% 0.18/0.38  fof(c_0_65, plain, ![X26, X27, X28]:(~v1_xboole_0(X26)|(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|v1_partfun1(X28,X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).
% 0.18/0.38  cnf(c_0_66, negated_conjecture, (esk8_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.18/0.38  cnf(c_0_67, negated_conjecture, (esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.18/0.38  cnf(c_0_68, plain, (v1_partfun1(X2,X1)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.18/0.38  cnf(c_0_69, negated_conjecture, (esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67])])).
% 0.18/0.38  cnf(c_0_70, negated_conjecture, (esk5_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_71, plain, (v1_partfun1(k1_xboole_0,X1)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_68, c_0_32])).
% 0.18/0.38  cnf(c_0_72, negated_conjecture, (~v1_partfun1(k1_xboole_0,esk5_0)), inference(rw,[status(thm)],[c_0_60, c_0_69])).
% 0.18/0.38  cnf(c_0_73, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_67])])).
% 0.18/0.38  cnf(c_0_74, plain, (v1_partfun1(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_71, c_0_30])).
% 0.18/0.38  cnf(c_0_75, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73]), c_0_74])]), ['proof']).
% 0.18/0.38  # SZS output end CNFRefutation
% 0.18/0.38  # Proof object total steps             : 76
% 0.18/0.38  # Proof object clause steps            : 54
% 0.18/0.38  # Proof object formula steps           : 22
% 0.18/0.38  # Proof object conjectures             : 33
% 0.18/0.38  # Proof object clause conjectures      : 30
% 0.18/0.38  # Proof object formula conjectures     : 3
% 0.18/0.38  # Proof object initial clauses used    : 20
% 0.18/0.38  # Proof object initial formulas used   : 11
% 0.18/0.38  # Proof object generating inferences   : 27
% 0.18/0.38  # Proof object simplifying inferences  : 24
% 0.18/0.38  # Training examples: 0 positive, 0 negative
% 0.18/0.38  # Parsed axioms                        : 12
% 0.18/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.38  # Initial clauses                      : 38
% 0.18/0.38  # Removed in clause preprocessing      : 1
% 0.18/0.38  # Initial clauses in saturation        : 37
% 0.18/0.38  # Processed clauses                    : 313
% 0.18/0.38  # ...of these trivial                  : 4
% 0.18/0.38  # ...subsumed                          : 94
% 0.18/0.38  # ...remaining for further processing  : 215
% 0.18/0.38  # Other redundant clauses eliminated   : 3
% 0.18/0.38  # Clauses deleted for lack of memory   : 0
% 0.18/0.38  # Backward-subsumed                    : 8
% 0.18/0.38  # Backward-rewritten                   : 121
% 0.18/0.38  # Generated clauses                    : 900
% 0.18/0.38  # ...of the previous two non-trivial   : 970
% 0.18/0.38  # Contextual simplify-reflections      : 9
% 0.18/0.38  # Paramodulations                      : 876
% 0.18/0.38  # Factorizations                       : 0
% 0.18/0.38  # Equation resolutions                 : 18
% 0.18/0.38  # Propositional unsat checks           : 0
% 0.18/0.38  #    Propositional check models        : 0
% 0.18/0.38  #    Propositional check unsatisfiable : 0
% 0.18/0.38  #    Propositional clauses             : 0
% 0.18/0.38  #    Propositional clauses after purity: 0
% 0.18/0.38  #    Propositional unsat core size     : 0
% 0.18/0.38  #    Propositional preprocessing time  : 0.000
% 0.18/0.38  #    Propositional encoding time       : 0.000
% 0.18/0.38  #    Propositional solver time         : 0.000
% 0.18/0.38  #    Success case prop preproc time    : 0.000
% 0.18/0.38  #    Success case prop encoding time   : 0.000
% 0.18/0.38  #    Success case prop solver time     : 0.000
% 0.18/0.38  # Current number of processed clauses  : 77
% 0.18/0.38  #    Positive orientable unit clauses  : 11
% 0.18/0.38  #    Positive unorientable unit clauses: 0
% 0.18/0.38  #    Negative unit clauses             : 0
% 0.18/0.38  #    Non-unit-clauses                  : 66
% 0.18/0.38  # Current number of unprocessed clauses: 665
% 0.18/0.38  # ...number of literals in the above   : 3197
% 0.18/0.38  # Current number of archived formulas  : 0
% 0.18/0.38  # Current number of archived clauses   : 135
% 0.18/0.38  # Clause-clause subsumption calls (NU) : 7621
% 0.18/0.38  # Rec. Clause-clause subsumption calls : 2965
% 0.18/0.38  # Non-unit clause-clause subsumptions  : 109
% 0.18/0.38  # Unit Clause-clause subsumption calls : 304
% 0.18/0.38  # Rewrite failures with RHS unbound    : 0
% 0.18/0.38  # BW rewrite match attempts            : 23
% 0.18/0.38  # BW rewrite match successes           : 6
% 0.18/0.38  # Condensation attempts                : 0
% 0.18/0.38  # Condensation successes               : 0
% 0.18/0.38  # Termbank termtop insertions          : 17743
% 0.18/0.38  
% 0.18/0.38  # -------------------------------------------------
% 0.18/0.38  # User time                : 0.057 s
% 0.18/0.38  # System time              : 0.006 s
% 0.18/0.38  # Total time               : 0.063 s
% 0.18/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
