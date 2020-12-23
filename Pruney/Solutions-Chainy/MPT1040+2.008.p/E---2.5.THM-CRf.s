%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:07 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 268 expanded)
%              Number of clauses        :   45 ( 107 expanded)
%              Number of leaves         :   12 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  269 (1659 expanded)
%              Number of equality atoms :   60 ( 368 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(rc1_xboole_0,axiom,(
    ? [X1] : v1_xboole_0(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_12,plain,(
    ! [X31,X32,X33,X34,X35,X37,X38,X39,X41] :
      ( ( v1_funct_1(esk4_5(X31,X32,X33,X34,X35))
        | ~ r2_hidden(X35,X34)
        | X34 != k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( m1_subset_1(esk4_5(X31,X32,X33,X34,X35),k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | ~ r2_hidden(X35,X34)
        | X34 != k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( esk4_5(X31,X32,X33,X34,X35) = X35
        | ~ r2_hidden(X35,X34)
        | X34 != k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( v1_partfun1(esk4_5(X31,X32,X33,X34,X35),X31)
        | ~ r2_hidden(X35,X34)
        | X34 != k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( r1_partfun1(X33,esk4_5(X31,X32,X33,X34,X35))
        | ~ r2_hidden(X35,X34)
        | X34 != k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( ~ v1_funct_1(X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | X38 != X37
        | ~ v1_partfun1(X38,X31)
        | ~ r1_partfun1(X33,X38)
        | r2_hidden(X37,X34)
        | X34 != k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( ~ r2_hidden(esk5_4(X31,X32,X33,X39),X39)
        | ~ v1_funct_1(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | X41 != esk5_4(X31,X32,X33,X39)
        | ~ v1_partfun1(X41,X31)
        | ~ r1_partfun1(X33,X41)
        | X39 = k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( v1_funct_1(esk6_4(X31,X32,X33,X39))
        | r2_hidden(esk5_4(X31,X32,X33,X39),X39)
        | X39 = k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( m1_subset_1(esk6_4(X31,X32,X33,X39),k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | r2_hidden(esk5_4(X31,X32,X33,X39),X39)
        | X39 = k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( esk6_4(X31,X32,X33,X39) = esk5_4(X31,X32,X33,X39)
        | r2_hidden(esk5_4(X31,X32,X33,X39),X39)
        | X39 = k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( v1_partfun1(esk6_4(X31,X32,X33,X39),X31)
        | r2_hidden(esk5_4(X31,X32,X33,X39),X39)
        | X39 = k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( r1_partfun1(X33,esk6_4(X31,X32,X33,X39))
        | r2_hidden(esk5_4(X31,X32,X33,X39),X39)
        | X39 = k5_partfun1(X31,X32,X33)
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X4,X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != X4
    | ~ v1_partfun1(X1,X2)
    | ~ r1_partfun1(X5,X1)
    | X6 != k5_partfun1(X2,X3,X5)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X21,X22] :
      ( ( k2_zfmisc_1(X21,X22) != k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( X21 != k1_xboole_0
        | k2_zfmisc_1(X21,X22) = k1_xboole_0 )
      & ( X22 != k1_xboole_0
        | k2_zfmisc_1(X21,X22) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_16,plain,(
    ! [X17] :
      ( ~ v1_xboole_0(X17)
      | X17 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_17,plain,(
    v1_xboole_0(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | X2 != k5_partfun1(X3,X4,X5)
    | ~ r1_partfun1(X5,X1)
    | ~ v1_partfun1(X1,X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(er,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,
    ( v1_funct_1(esk9_0)
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))
    & v1_funct_1(esk10_0)
    & v1_funct_2(esk10_0,esk7_0,esk8_0)
    & m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))
    & r1_partfun1(esk9_0,esk10_0)
    & ( esk8_0 != k1_xboole_0
      | esk7_0 = k1_xboole_0 )
    & ~ r2_hidden(esk10_0,k5_partfun1(esk7_0,esk8_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_20,plain,(
    ! [X43] :
      ( v1_partfun1(k6_partfun1(X43),X43)
      & m1_subset_1(k6_partfun1(X43),k1_zfmisc_1(k2_zfmisc_1(X43,X43))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_21,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_25,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_26,plain,(
    ! [X28,X29,X30] :
      ( ( v1_funct_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X28,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
        | v1_xboole_0(X29) )
      & ( v1_partfun1(X30,X28)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X28,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
        | v1_xboole_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ r1_partfun1(X4,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X25,X26,X27] :
      ( ~ r2_hidden(X25,X26)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X27))
      | ~ v1_xboole_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_31,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_34,plain,(
    ! [X19,X20] :
      ( ( r1_tarski(X19,X20)
        | X19 != X20 )
      & ( r1_tarski(X20,X19)
        | X19 != X20 )
      & ( ~ r1_tarski(X19,X20)
        | ~ r1_tarski(X20,X19)
        | X19 = X20 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_37,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X23,k1_zfmisc_1(X24))
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | m1_subset_1(X23,k1_zfmisc_1(X24)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_38,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_2(esk10_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk7_0,esk8_0,esk9_0))
    | ~ r1_partfun1(esk9_0,X1)
    | ~ v1_partfun1(X1,esk7_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_43,negated_conjecture,
    ( r1_partfun1(esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(esk10_0,k5_partfun1(esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_47,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_33])).

cnf(c_0_48,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( v1_partfun1(esk10_0,esk7_0)
    | v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_partfun1(esk10_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_41]),c_0_39])]),c_0_44])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,k6_partfun1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_54,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk10_0,k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_39])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(esk8_0) ),
    inference(sr,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_59,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,esk8_0) = esk10_0
    | ~ v1_xboole_0(k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_57])).

cnf(c_0_62,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_64,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_65,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( esk10_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_61]),c_0_62]),c_0_47])])).

cnf(c_0_67,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_61])])).

cnf(c_0_68,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_66]),c_0_67]),c_0_68])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.20/0.43  # and selection function SelectNewComplexAHP.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.029 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(d7_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(X4=k5_partfun1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>?[X6]:((((v1_funct_1(X6)&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&X6=X5)&v1_partfun1(X6,X1))&r1_partfun1(X3,X6))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 0.20/0.43  fof(t155_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_hidden(X4,k5_partfun1(X1,X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_2)).
% 0.20/0.43  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.43  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.43  fof(rc1_xboole_0, axiom, ?[X1]:v1_xboole_0(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 0.20/0.43  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.20/0.43  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.43  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.20/0.43  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.43  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.43  fof(c_0_12, plain, ![X31, X32, X33, X34, X35, X37, X38, X39, X41]:(((((((v1_funct_1(esk4_5(X31,X32,X33,X34,X35))|~r2_hidden(X35,X34)|X34!=k5_partfun1(X31,X32,X33)|(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))&(m1_subset_1(esk4_5(X31,X32,X33,X34,X35),k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|~r2_hidden(X35,X34)|X34!=k5_partfun1(X31,X32,X33)|(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))))&(esk4_5(X31,X32,X33,X34,X35)=X35|~r2_hidden(X35,X34)|X34!=k5_partfun1(X31,X32,X33)|(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))))&(v1_partfun1(esk4_5(X31,X32,X33,X34,X35),X31)|~r2_hidden(X35,X34)|X34!=k5_partfun1(X31,X32,X33)|(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))))&(r1_partfun1(X33,esk4_5(X31,X32,X33,X34,X35))|~r2_hidden(X35,X34)|X34!=k5_partfun1(X31,X32,X33)|(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))))&(~v1_funct_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|X38!=X37|~v1_partfun1(X38,X31)|~r1_partfun1(X33,X38)|r2_hidden(X37,X34)|X34!=k5_partfun1(X31,X32,X33)|(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))))&((~r2_hidden(esk5_4(X31,X32,X33,X39),X39)|(~v1_funct_1(X41)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|X41!=esk5_4(X31,X32,X33,X39)|~v1_partfun1(X41,X31)|~r1_partfun1(X33,X41))|X39=k5_partfun1(X31,X32,X33)|(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))&(((((v1_funct_1(esk6_4(X31,X32,X33,X39))|r2_hidden(esk5_4(X31,X32,X33,X39),X39)|X39=k5_partfun1(X31,X32,X33)|(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))&(m1_subset_1(esk6_4(X31,X32,X33,X39),k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|r2_hidden(esk5_4(X31,X32,X33,X39),X39)|X39=k5_partfun1(X31,X32,X33)|(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))))&(esk6_4(X31,X32,X33,X39)=esk5_4(X31,X32,X33,X39)|r2_hidden(esk5_4(X31,X32,X33,X39),X39)|X39=k5_partfun1(X31,X32,X33)|(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))))&(v1_partfun1(esk6_4(X31,X32,X33,X39),X31)|r2_hidden(esk5_4(X31,X32,X33,X39),X39)|X39=k5_partfun1(X31,X32,X33)|(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))))&(r1_partfun1(X33,esk6_4(X31,X32,X33,X39))|r2_hidden(esk5_4(X31,X32,X33,X39),X39)|X39=k5_partfun1(X31,X32,X33)|(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).
% 0.20/0.43  cnf(c_0_13, plain, (r2_hidden(X4,X6)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X1!=X4|~v1_partfun1(X1,X2)|~r1_partfun1(X5,X1)|X6!=k5_partfun1(X2,X3,X5)|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_hidden(X4,k5_partfun1(X1,X2,X3))))))), inference(assume_negation,[status(cth)],[t155_funct_2])).
% 0.20/0.43  fof(c_0_15, plain, ![X21, X22]:((k2_zfmisc_1(X21,X22)!=k1_xboole_0|(X21=k1_xboole_0|X22=k1_xboole_0))&((X21!=k1_xboole_0|k2_zfmisc_1(X21,X22)=k1_xboole_0)&(X22!=k1_xboole_0|k2_zfmisc_1(X21,X22)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.43  fof(c_0_16, plain, ![X17]:(~v1_xboole_0(X17)|X17=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.43  fof(c_0_17, plain, v1_xboole_0(esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).
% 0.20/0.43  cnf(c_0_18, plain, (r2_hidden(X1,X2)|X2!=k5_partfun1(X3,X4,X5)|~r1_partfun1(X5,X1)|~v1_partfun1(X1,X3)|~v1_funct_1(X5)|~v1_funct_1(X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(er,[status(thm)],[c_0_13])).
% 0.20/0.43  fof(c_0_19, negated_conjecture, ((v1_funct_1(esk9_0)&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))))&(((v1_funct_1(esk10_0)&v1_funct_2(esk10_0,esk7_0,esk8_0))&m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))))&(r1_partfun1(esk9_0,esk10_0)&((esk8_0!=k1_xboole_0|esk7_0=k1_xboole_0)&~r2_hidden(esk10_0,k5_partfun1(esk7_0,esk8_0,esk9_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.20/0.43  fof(c_0_20, plain, ![X43]:(v1_partfun1(k6_partfun1(X43),X43)&m1_subset_1(k6_partfun1(X43),k1_zfmisc_1(k2_zfmisc_1(X43,X43)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.20/0.43  cnf(c_0_21, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.43  cnf(c_0_22, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.43  cnf(c_0_23, plain, (v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  fof(c_0_24, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.43  fof(c_0_25, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.43  fof(c_0_26, plain, ![X28, X29, X30]:((v1_funct_1(X30)|(~v1_funct_1(X30)|~v1_funct_2(X30,X28,X29))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|v1_xboole_0(X29))&(v1_partfun1(X30,X28)|(~v1_funct_1(X30)|~v1_funct_2(X30,X28,X29))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|v1_xboole_0(X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.20/0.43  cnf(c_0_27, plain, (r2_hidden(X1,k5_partfun1(X2,X3,X4))|~r1_partfun1(X4,X1)|~v1_partfun1(X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(er,[status(thm)],[c_0_18])).
% 0.20/0.43  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  fof(c_0_30, plain, ![X25, X26, X27]:(~r2_hidden(X25,X26)|~m1_subset_1(X26,k1_zfmisc_1(X27))|~v1_xboole_0(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.43  cnf(c_0_31, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_32, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_33, plain, (esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.43  fof(c_0_34, plain, ![X19, X20]:(((r1_tarski(X19,X20)|X19!=X20)&(r1_tarski(X20,X19)|X19!=X20))&(~r1_tarski(X19,X20)|~r1_tarski(X20,X19)|X19=X20)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.43  cnf(c_0_35, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.43  cnf(c_0_36, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.43  fof(c_0_37, plain, ![X23, X24]:((~m1_subset_1(X23,k1_zfmisc_1(X24))|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|m1_subset_1(X23,k1_zfmisc_1(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.43  cnf(c_0_38, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.43  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_40, negated_conjecture, (v1_funct_2(esk10_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_41, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_42, negated_conjecture, (r2_hidden(X1,k5_partfun1(esk7_0,esk8_0,esk9_0))|~r1_partfun1(esk9_0,X1)|~v1_partfun1(X1,esk7_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.20/0.43  cnf(c_0_43, negated_conjecture, (r1_partfun1(esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_44, negated_conjecture, (~r2_hidden(esk10_0,k5_partfun1(esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_45, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.43  cnf(c_0_46, plain, (m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.43  cnf(c_0_47, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_23, c_0_33])).
% 0.20/0.43  cnf(c_0_48, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.43  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.43  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.43  cnf(c_0_51, negated_conjecture, (v1_partfun1(esk10_0,esk7_0)|v1_xboole_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41])])).
% 0.20/0.43  cnf(c_0_52, negated_conjecture, (~v1_partfun1(esk10_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_41]), c_0_39])]), c_0_44])).
% 0.20/0.43  cnf(c_0_53, plain, (~r2_hidden(X1,k6_partfun1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.20/0.43  cnf(c_0_54, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.43  cnf(c_0_55, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.43  cnf(c_0_56, negated_conjecture, (r1_tarski(esk10_0,k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_50, c_0_39])).
% 0.20/0.43  cnf(c_0_57, negated_conjecture, (v1_xboole_0(esk8_0)), inference(sr,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.43  cnf(c_0_58, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.43  cnf(c_0_59, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.43  cnf(c_0_60, negated_conjecture, (k2_zfmisc_1(esk7_0,esk8_0)=esk10_0|~v1_xboole_0(k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.43  cnf(c_0_61, negated_conjecture, (esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_57])).
% 0.20/0.43  cnf(c_0_62, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_58])).
% 0.20/0.43  cnf(c_0_63, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_64, plain, (v1_partfun1(k6_partfun1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_65, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_59])).
% 0.20/0.43  cnf(c_0_66, negated_conjecture, (esk10_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_61]), c_0_62]), c_0_47])])).
% 0.20/0.43  cnf(c_0_67, negated_conjecture, (esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_61])])).
% 0.20/0.43  cnf(c_0_68, plain, (v1_partfun1(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.43  cnf(c_0_69, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_66]), c_0_67]), c_0_68])]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 70
% 0.20/0.43  # Proof object clause steps            : 45
% 0.20/0.43  # Proof object formula steps           : 25
% 0.20/0.43  # Proof object conjectures             : 21
% 0.20/0.43  # Proof object clause conjectures      : 18
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 22
% 0.20/0.43  # Proof object initial formulas used   : 12
% 0.20/0.43  # Proof object generating inferences   : 17
% 0.20/0.43  # Proof object simplifying inferences  : 26
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 12
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 40
% 0.20/0.43  # Removed in clause preprocessing      : 1
% 0.20/0.43  # Initial clauses in saturation        : 39
% 0.20/0.43  # Processed clauses                    : 563
% 0.20/0.43  # ...of these trivial                  : 6
% 0.20/0.43  # ...subsumed                          : 253
% 0.20/0.43  # ...remaining for further processing  : 303
% 0.20/0.43  # Other redundant clauses eliminated   : 17
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 1
% 0.20/0.43  # Backward-rewritten                   : 172
% 0.20/0.43  # Generated clauses                    : 825
% 0.20/0.43  # ...of the previous two non-trivial   : 931
% 0.20/0.43  # Contextual simplify-reflections      : 2
% 0.20/0.43  # Paramodulations                      : 798
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 26
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 88
% 0.20/0.43  #    Positive orientable unit clauses  : 20
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 2
% 0.20/0.43  #    Non-unit-clauses                  : 66
% 0.20/0.43  # Current number of unprocessed clauses: 445
% 0.20/0.43  # ...number of literals in the above   : 2012
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 212
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 16819
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 4761
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 249
% 0.20/0.43  # Unit Clause-clause subsumption calls : 159
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 11
% 0.20/0.43  # BW rewrite match successes           : 7
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 21339
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.085 s
% 0.20/0.43  # System time              : 0.005 s
% 0.20/0.43  # Total time               : 0.090 s
% 0.20/0.43  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
