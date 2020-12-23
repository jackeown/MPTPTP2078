%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1040+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:37 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 189 expanded)
%              Number of clauses        :   24 (  68 expanded)
%              Number of leaves         :    5 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :  186 (1361 expanded)
%              Number of equality atoms :   34 ( 277 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(c_0_5,negated_conjecture,(
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

fof(c_0_6,plain,(
    ! [X10,X11,X12] :
      ( ( v1_funct_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | v1_xboole_0(X11) )
      & ( v1_partfun1(X12,X10)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | v1_xboole_0(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_7,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk4_0,esk5_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & r1_partfun1(esk6_0,esk7_0)
    & ( esk5_0 != k1_xboole_0
      | esk4_0 = k1_xboole_0 )
    & ~ r2_hidden(esk7_0,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X13,X14,X15,X16,X17,X19,X20,X21,X23] :
      ( ( v1_funct_1(esk1_5(X13,X14,X15,X16,X17))
        | ~ r2_hidden(X17,X16)
        | X16 != k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( m1_subset_1(esk1_5(X13,X14,X15,X16,X17),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | ~ r2_hidden(X17,X16)
        | X16 != k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( esk1_5(X13,X14,X15,X16,X17) = X17
        | ~ r2_hidden(X17,X16)
        | X16 != k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( v1_partfun1(esk1_5(X13,X14,X15,X16,X17),X13)
        | ~ r2_hidden(X17,X16)
        | X16 != k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( r1_partfun1(X15,esk1_5(X13,X14,X15,X16,X17))
        | ~ r2_hidden(X17,X16)
        | X16 != k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | X20 != X19
        | ~ v1_partfun1(X20,X13)
        | ~ r1_partfun1(X15,X20)
        | r2_hidden(X19,X16)
        | X16 != k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( ~ r2_hidden(esk2_4(X13,X14,X15,X21),X21)
        | ~ v1_funct_1(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | X23 != esk2_4(X13,X14,X15,X21)
        | ~ v1_partfun1(X23,X13)
        | ~ r1_partfun1(X15,X23)
        | X21 = k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( v1_funct_1(esk3_4(X13,X14,X15,X21))
        | r2_hidden(esk2_4(X13,X14,X15,X21),X21)
        | X21 = k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( m1_subset_1(esk3_4(X13,X14,X15,X21),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | r2_hidden(esk2_4(X13,X14,X15,X21),X21)
        | X21 = k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( esk3_4(X13,X14,X15,X21) = esk2_4(X13,X14,X15,X21)
        | r2_hidden(esk2_4(X13,X14,X15,X21),X21)
        | X21 = k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( v1_partfun1(esk3_4(X13,X14,X15,X21),X13)
        | r2_hidden(esk2_4(X13,X14,X15,X21),X21)
        | X21 = k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( r1_partfun1(X15,esk3_4(X13,X14,X15,X21))
        | r2_hidden(esk2_4(X13,X14,X15,X21),X21)
        | X21 = k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

fof(c_0_9,plain,(
    ! [X25] :
      ( ~ v1_xboole_0(X25)
      | X25 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_10,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r2_hidden(X4,X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != X4
    | ~ v1_partfun1(X1,X2)
    | ~ r1_partfun1(X5,X1)
    | X6 != k5_partfun1(X2,X3,X5)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v1_partfun1(esk7_0,esk4_0)
    | v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ r1_partfun1(X4,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_14])])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_20,plain,(
    ! [X7,X8,X9] :
      ( ~ v1_xboole_0(X7)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_partfun1(X9,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

cnf(c_0_21,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v1_partfun1(esk7_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0))
    | ~ r1_partfun1(esk6_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_24,negated_conjecture,
    ( r1_partfun1(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_partfun1(esk7_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_partfun1(esk7_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_11]),c_0_24]),c_0_13])]),c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( v1_partfun1(esk7_0,esk4_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( v1_partfun1(esk7_0,esk4_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( v1_partfun1(esk7_0,esk4_0)
    | v1_partfun1(esk7_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_27]),c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_partfun1(esk7_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_28,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_32,c_0_28]),c_0_33]),
    [proof]).

%------------------------------------------------------------------------------
