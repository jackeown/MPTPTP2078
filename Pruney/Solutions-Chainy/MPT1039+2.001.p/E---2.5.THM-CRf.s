%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:05 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   40 (1091 expanded)
%              Number of clauses        :   33 ( 353 expanded)
%              Number of leaves         :    3 ( 270 expanded)
%              Depth                    :   16
%              Number of atoms          :  277 (13296 expanded)
%              Number of equality atoms :   37 (2042 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   70 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t154_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ~ ( ( X2 = k1_xboole_0
               => X1 = k1_xboole_0 )
              & r1_partfun1(X3,X4)
              & ! [X5] :
                  ( ( v1_funct_1(X5)
                    & v1_funct_2(X5,X1,X2)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                 => ~ ( r1_partfun1(X3,X5)
                      & r1_partfun1(X4,X5) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_2)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(t162_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ~ ( ( X2 = k1_xboole_0
               => X1 = k1_xboole_0 )
              & r1_partfun1(X3,X4)
              & ! [X5] :
                  ( ( v1_funct_1(X5)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                 => ~ ( v1_partfun1(X5,X1)
                      & r1_partfun1(X3,X5)
                      & r1_partfun1(X4,X5) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_partfun1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ~ ( ( X2 = k1_xboole_0
                 => X1 = k1_xboole_0 )
                & r1_partfun1(X3,X4)
                & ! [X5] :
                    ( ( v1_funct_1(X5)
                      & v1_funct_2(X5,X1,X2)
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                   => ~ ( r1_partfun1(X3,X5)
                        & r1_partfun1(X4,X5) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t154_funct_2])).

fof(c_0_4,negated_conjecture,(
    ! [X18] :
      ( v1_funct_1(esk4_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & v1_funct_1(esk5_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & ( esk3_0 != k1_xboole_0
        | esk2_0 = k1_xboole_0 )
      & r1_partfun1(esk4_0,esk5_0)
      & ( ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,esk2_0,esk3_0)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
        | ~ r1_partfun1(esk4_0,X18)
        | ~ r1_partfun1(esk5_0,X18) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

fof(c_0_5,plain,(
    ! [X6,X7,X8] :
      ( ( v1_funct_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_partfun1(X8,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( v1_funct_2(X8,X6,X7)
        | ~ v1_funct_1(X8)
        | ~ v1_partfun1(X8,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_6,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,esk2_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    | ~ r1_partfun1(esk4_0,X1)
    | ~ r1_partfun1(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X9,X10,X11,X12] :
      ( ( v1_funct_1(esk1_4(X9,X10,X11,X12))
        | X10 = k1_xboole_0
        | ~ r1_partfun1(X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( m1_subset_1(esk1_4(X9,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | X10 = k1_xboole_0
        | ~ r1_partfun1(X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( v1_partfun1(esk1_4(X9,X10,X11,X12),X9)
        | X10 = k1_xboole_0
        | ~ r1_partfun1(X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( r1_partfun1(X11,esk1_4(X9,X10,X11,X12))
        | X10 = k1_xboole_0
        | ~ r1_partfun1(X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( r1_partfun1(X12,esk1_4(X9,X10,X11,X12))
        | X10 = k1_xboole_0
        | ~ r1_partfun1(X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( v1_funct_1(esk1_4(X9,X10,X11,X12))
        | X9 != k1_xboole_0
        | ~ r1_partfun1(X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( m1_subset_1(esk1_4(X9,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | X9 != k1_xboole_0
        | ~ r1_partfun1(X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( v1_partfun1(esk1_4(X9,X10,X11,X12),X9)
        | X9 != k1_xboole_0
        | ~ r1_partfun1(X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( r1_partfun1(X11,esk1_4(X9,X10,X11,X12))
        | X9 != k1_xboole_0
        | ~ r1_partfun1(X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( r1_partfun1(X12,esk1_4(X9,X10,X11,X12))
        | X9 != k1_xboole_0
        | ~ r1_partfun1(X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_partfun1])])])])])).

cnf(c_0_9,negated_conjecture,
    ( ~ r1_partfun1(esk4_0,X1)
    | ~ r1_partfun1(esk5_0,X1)
    | ~ v1_partfun1(X1,esk2_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( r1_partfun1(X1,esk1_4(X2,X3,X1,X4))
    | X3 = k1_xboole_0
    | ~ r1_partfun1(X1,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r1_partfun1(esk5_0,esk1_4(X2,X1,esk4_0,X3))
    | ~ r1_partfun1(esk4_0,X3)
    | ~ v1_partfun1(esk1_4(X2,X1,esk4_0,X3),esk2_0)
    | ~ v1_funct_1(esk1_4(X2,X1,esk4_0,X3))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(esk1_4(X2,X1,esk4_0,X3),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_13,plain,
    ( v1_partfun1(esk1_4(X1,X2,X3,X4),X1)
    | X2 = k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r1_partfun1(esk5_0,esk1_4(esk2_0,X1,esk4_0,X2))
    | ~ r1_partfun1(esk4_0,X2)
    | ~ v1_funct_1(esk1_4(esk2_0,X1,esk4_0,X2))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(esk1_4(esk2_0,X1,esk4_0,X2),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_11])])).

cnf(c_0_15,plain,
    ( r1_partfun1(X1,esk1_4(X2,X3,X4,X1))
    | X3 = k1_xboole_0
    | ~ r1_partfun1(X4,X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( r1_partfun1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ v1_funct_1(esk1_4(esk2_0,X1,esk4_0,esk5_0))
    | ~ m1_subset_1(esk1_4(esk2_0,X1,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_11])])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X2 = k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_22,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_funct_1(esk1_4(esk2_0,esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_16]),c_0_17]),c_0_11])])).

cnf(c_0_23,plain,
    ( v1_funct_1(esk1_4(X1,X2,X3,X4))
    | X2 = k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_25,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_16]),c_0_17]),c_0_11]),c_0_21]),c_0_20])])).

cnf(c_0_26,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_partfun1(esk4_0,X1)
    | ~ r1_partfun1(esk5_0,X1)
    | ~ v1_partfun1(X1,k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_28,plain,
    ( r1_partfun1(X1,esk1_4(X2,X3,X1,X4))
    | X2 != k1_xboole_0
    | ~ r1_partfun1(X1,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ r1_partfun1(esk5_0,esk1_4(X1,X2,esk4_0,X3))
    | ~ r1_partfun1(esk4_0,X3)
    | ~ v1_partfun1(esk1_4(X1,X2,esk4_0,X3),k1_xboole_0)
    | ~ v1_funct_1(esk1_4(X1,X2,esk4_0,X3))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(esk1_4(X1,X2,esk4_0,X3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_11])])).

cnf(c_0_30,plain,
    ( v1_partfun1(esk1_4(X1,X2,X3,X4),X1)
    | X1 != k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_partfun1(esk5_0,esk1_4(k1_xboole_0,X1,esk4_0,X2))
    | ~ r1_partfun1(esk4_0,X2)
    | ~ v1_funct_1(esk1_4(k1_xboole_0,X1,esk4_0,X2))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(esk1_4(k1_xboole_0,X1,esk4_0,X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_11])])).

cnf(c_0_32,plain,
    ( r1_partfun1(X1,esk1_4(X2,X3,X4,X1))
    | X2 != k1_xboole_0
    | ~ r1_partfun1(X4,X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_funct_1(esk1_4(k1_xboole_0,X1,esk4_0,esk5_0))
    | ~ m1_subset_1(esk1_4(k1_xboole_0,X1,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_16]),c_0_17]),c_0_11])])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X1 != k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_25]),c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_25]),c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_funct_1(esk1_4(k1_xboole_0,k1_xboole_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_16]),c_0_17]),c_0_11])])).

cnf(c_0_38,plain,
    ( v1_funct_1(esk1_4(X1,X2,X3,X4))
    | X1 != k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_16]),c_0_17]),c_0_11]),c_0_36]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t154_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~((((X2=k1_xboole_0=>X1=k1_xboole_0)&r1_partfun1(X3,X4))&![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~((r1_partfun1(X3,X5)&r1_partfun1(X4,X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_2)).
% 0.13/0.38  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.13/0.38  fof(t162_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~((((X2=k1_xboole_0=>X1=k1_xboole_0)&r1_partfun1(X3,X4))&![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~(((v1_partfun1(X5,X1)&r1_partfun1(X3,X5))&r1_partfun1(X4,X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_partfun1)).
% 0.13/0.38  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~((((X2=k1_xboole_0=>X1=k1_xboole_0)&r1_partfun1(X3,X4))&![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~((r1_partfun1(X3,X5)&r1_partfun1(X4,X5))))))))), inference(assume_negation,[status(cth)],[t154_funct_2])).
% 0.13/0.38  fof(c_0_4, negated_conjecture, ![X18]:((v1_funct_1(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&((v1_funct_1(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(((esk3_0!=k1_xboole_0|esk2_0=k1_xboole_0)&r1_partfun1(esk4_0,esk5_0))&(~v1_funct_1(X18)|~v1_funct_2(X18,esk2_0,esk3_0)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))|(~r1_partfun1(esk4_0,X18)|~r1_partfun1(esk5_0,X18)))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).
% 0.13/0.38  fof(c_0_5, plain, ![X6, X7, X8]:((v1_funct_1(X8)|(~v1_funct_1(X8)|~v1_partfun1(X8,X6))|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))&(v1_funct_2(X8,X6,X7)|(~v1_funct_1(X8)|~v1_partfun1(X8,X6))|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.13/0.38  cnf(c_0_6, negated_conjecture, (~v1_funct_1(X1)|~v1_funct_2(X1,esk2_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))|~r1_partfun1(esk4_0,X1)|~r1_partfun1(esk5_0,X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_7, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  fof(c_0_8, plain, ![X9, X10, X11, X12]:((((v1_funct_1(esk1_4(X9,X10,X11,X12))|(X10=k1_xboole_0|~r1_partfun1(X11,X12))|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))&(m1_subset_1(esk1_4(X9,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|(X10=k1_xboole_0|~r1_partfun1(X11,X12))|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))))&(((v1_partfun1(esk1_4(X9,X10,X11,X12),X9)|(X10=k1_xboole_0|~r1_partfun1(X11,X12))|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))&(r1_partfun1(X11,esk1_4(X9,X10,X11,X12))|(X10=k1_xboole_0|~r1_partfun1(X11,X12))|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))))&(r1_partfun1(X12,esk1_4(X9,X10,X11,X12))|(X10=k1_xboole_0|~r1_partfun1(X11,X12))|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))))&(((v1_funct_1(esk1_4(X9,X10,X11,X12))|(X9!=k1_xboole_0|~r1_partfun1(X11,X12))|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))&(m1_subset_1(esk1_4(X9,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|(X9!=k1_xboole_0|~r1_partfun1(X11,X12))|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))))&(((v1_partfun1(esk1_4(X9,X10,X11,X12),X9)|(X9!=k1_xboole_0|~r1_partfun1(X11,X12))|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))&(r1_partfun1(X11,esk1_4(X9,X10,X11,X12))|(X9!=k1_xboole_0|~r1_partfun1(X11,X12))|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))))&(r1_partfun1(X12,esk1_4(X9,X10,X11,X12))|(X9!=k1_xboole_0|~r1_partfun1(X11,X12))|(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10))))|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_partfun1])])])])])).
% 0.13/0.38  cnf(c_0_9, negated_conjecture, (~r1_partfun1(esk4_0,X1)|~r1_partfun1(esk5_0,X1)|~v1_partfun1(X1,esk2_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.13/0.38  cnf(c_0_10, plain, (r1_partfun1(X1,esk1_4(X2,X3,X1,X4))|X3=k1_xboole_0|~r1_partfun1(X1,X4)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_11, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_12, negated_conjecture, (X1=k1_xboole_0|~r1_partfun1(esk5_0,esk1_4(X2,X1,esk4_0,X3))|~r1_partfun1(esk4_0,X3)|~v1_partfun1(esk1_4(X2,X1,esk4_0,X3),esk2_0)|~v1_funct_1(esk1_4(X2,X1,esk4_0,X3))|~v1_funct_1(X3)|~m1_subset_1(esk1_4(X2,X1,esk4_0,X3),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])])).
% 0.13/0.38  cnf(c_0_13, plain, (v1_partfun1(esk1_4(X1,X2,X3,X4),X1)|X2=k1_xboole_0|~r1_partfun1(X3,X4)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (X1=k1_xboole_0|~r1_partfun1(esk5_0,esk1_4(esk2_0,X1,esk4_0,X2))|~r1_partfun1(esk4_0,X2)|~v1_funct_1(esk1_4(esk2_0,X1,esk4_0,X2))|~v1_funct_1(X2)|~m1_subset_1(esk1_4(esk2_0,X1,esk4_0,X2),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_11])])).
% 0.13/0.38  cnf(c_0_15, plain, (r1_partfun1(X1,esk1_4(X2,X3,X4,X1))|X3=k1_xboole_0|~r1_partfun1(X4,X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (r1_partfun1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (X1=k1_xboole_0|~v1_funct_1(esk1_4(esk2_0,X1,esk4_0,esk5_0))|~m1_subset_1(esk1_4(esk2_0,X1,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17]), c_0_11])])).
% 0.13/0.38  cnf(c_0_19, plain, (m1_subset_1(esk1_4(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|X2=k1_xboole_0|~r1_partfun1(X3,X4)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (esk3_0=k1_xboole_0|~v1_funct_1(esk1_4(esk2_0,esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_16]), c_0_17]), c_0_11])])).
% 0.13/0.38  cnf(c_0_23, plain, (v1_funct_1(esk1_4(X1,X2,X3,X4))|X2=k1_xboole_0|~r1_partfun1(X3,X4)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_16]), c_0_17]), c_0_11]), c_0_21]), c_0_20])])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25])])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (~r1_partfun1(esk4_0,X1)|~r1_partfun1(esk5_0,X1)|~v1_partfun1(X1,k1_xboole_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9, c_0_25]), c_0_26]), c_0_26])).
% 0.13/0.38  cnf(c_0_28, plain, (r1_partfun1(X1,esk1_4(X2,X3,X1,X4))|X2!=k1_xboole_0|~r1_partfun1(X1,X4)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (X1!=k1_xboole_0|~r1_partfun1(esk5_0,esk1_4(X1,X2,esk4_0,X3))|~r1_partfun1(esk4_0,X3)|~v1_partfun1(esk1_4(X1,X2,esk4_0,X3),k1_xboole_0)|~v1_funct_1(esk1_4(X1,X2,esk4_0,X3))|~v1_funct_1(X3)|~m1_subset_1(esk1_4(X1,X2,esk4_0,X3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_11])])).
% 0.13/0.38  cnf(c_0_30, plain, (v1_partfun1(esk1_4(X1,X2,X3,X4),X1)|X1!=k1_xboole_0|~r1_partfun1(X3,X4)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (~r1_partfun1(esk5_0,esk1_4(k1_xboole_0,X1,esk4_0,X2))|~r1_partfun1(esk4_0,X2)|~v1_funct_1(esk1_4(k1_xboole_0,X1,esk4_0,X2))|~v1_funct_1(X2)|~m1_subset_1(esk1_4(k1_xboole_0,X1,esk4_0,X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_11])])).
% 0.13/0.38  cnf(c_0_32, plain, (r1_partfun1(X1,esk1_4(X2,X3,X4,X1))|X2!=k1_xboole_0|~r1_partfun1(X4,X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (~v1_funct_1(esk1_4(k1_xboole_0,X1,esk4_0,esk5_0))|~m1_subset_1(esk1_4(k1_xboole_0,X1,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_16]), c_0_17]), c_0_11])])).
% 0.13/0.38  cnf(c_0_34, plain, (m1_subset_1(esk1_4(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|X1!=k1_xboole_0|~r1_partfun1(X3,X4)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_25]), c_0_26])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_25]), c_0_26])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (~v1_funct_1(esk1_4(k1_xboole_0,k1_xboole_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_16]), c_0_17]), c_0_11])])).
% 0.13/0.38  cnf(c_0_38, plain, (v1_funct_1(esk1_4(X1,X2,X3,X4))|X1!=k1_xboole_0|~r1_partfun1(X3,X4)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_16]), c_0_17]), c_0_11]), c_0_36]), c_0_35])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 40
% 0.13/0.38  # Proof object clause steps            : 33
% 0.13/0.38  # Proof object formula steps           : 7
% 0.13/0.38  # Proof object conjectures             : 25
% 0.13/0.38  # Proof object clause conjectures      : 22
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 18
% 0.13/0.38  # Proof object initial formulas used   : 3
% 0.13/0.38  # Proof object generating inferences   : 11
% 0.13/0.38  # Proof object simplifying inferences  : 49
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 3
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 19
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 18
% 0.13/0.38  # Processed clauses                    : 75
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 12
% 0.13/0.38  # ...remaining for further processing  : 63
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 3
% 0.13/0.38  # Backward-rewritten                   : 10
% 0.13/0.38  # Generated clauses                    : 38
% 0.13/0.38  # ...of the previous two non-trivial   : 46
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 38
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 32
% 0.13/0.38  #    Positive orientable unit clauses  : 7
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 23
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 31
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 674
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 47
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 15
% 0.13/0.38  # Unit Clause-clause subsumption calls : 40
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 2
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4541
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.033 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.037 s
% 0.13/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
