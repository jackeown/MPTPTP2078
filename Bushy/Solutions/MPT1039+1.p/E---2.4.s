%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t154_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:32 EDT 2019

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (6174 expanded)
%              Number of clauses        :   51 (2034 expanded)
%              Number of leaves         :    3 (1468 expanded)
%              Depth                    :   13
%              Number of atoms          :  320 (67594 expanded)
%              Number of equality atoms :   43 (10787 expanded)
%              Maximal formula depth    :   21 (   5 average)
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
    file('/export/starexec/sandbox/benchmark/funct_2__t154_funct_2.p',t154_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/funct_2__t154_funct_2.p',t162_partfun1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t154_funct_2.p',cc1_funct_2)).

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

fof(c_0_4,plain,(
    ! [X19,X20,X21,X22] :
      ( ( v1_funct_1(esk6_4(X19,X20,X21,X22))
        | X20 = k1_xboole_0
        | ~ r1_partfun1(X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( m1_subset_1(esk6_4(X19,X20,X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | X20 = k1_xboole_0
        | ~ r1_partfun1(X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( v1_partfun1(esk6_4(X19,X20,X21,X22),X19)
        | X20 = k1_xboole_0
        | ~ r1_partfun1(X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( r1_partfun1(X21,esk6_4(X19,X20,X21,X22))
        | X20 = k1_xboole_0
        | ~ r1_partfun1(X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( r1_partfun1(X22,esk6_4(X19,X20,X21,X22))
        | X20 = k1_xboole_0
        | ~ r1_partfun1(X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( v1_funct_1(esk6_4(X19,X20,X21,X22))
        | X19 != k1_xboole_0
        | ~ r1_partfun1(X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( m1_subset_1(esk6_4(X19,X20,X21,X22),k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | X19 != k1_xboole_0
        | ~ r1_partfun1(X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( v1_partfun1(esk6_4(X19,X20,X21,X22),X19)
        | X19 != k1_xboole_0
        | ~ r1_partfun1(X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( r1_partfun1(X21,esk6_4(X19,X20,X21,X22))
        | X19 != k1_xboole_0
        | ~ r1_partfun1(X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( r1_partfun1(X22,esk6_4(X19,X20,X21,X22))
        | X19 != k1_xboole_0
        | ~ r1_partfun1(X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_partfun1])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X10] :
      ( v1_funct_1(esk3_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
      & v1_funct_1(esk4_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
      & ( esk2_0 != k1_xboole_0
        | esk1_0 = k1_xboole_0 )
      & r1_partfun1(esk3_0,esk4_0)
      & ( ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,esk1_0,esk2_0)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
        | ~ r1_partfun1(esk3_0,X10)
        | ~ r1_partfun1(esk4_0,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

cnf(c_0_6,plain,
    ( m1_subset_1(esk6_4(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X2 = k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v1_funct_1(esk6_4(X1,X2,X3,X4))
    | X2 = k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( v1_partfun1(esk6_4(X1,X2,X3,X4),X1)
    | X2 = k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_11,plain,(
    ! [X41,X42,X43] :
      ( ( v1_funct_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v1_partfun1(X43,X41)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( v1_funct_2(X43,X41,X42)
        | ~ v1_funct_1(X43)
        | ~ v1_partfun1(X43,X41)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_12,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | m1_subset_1(esk6_4(esk1_0,esk2_0,X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ r1_partfun1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( r1_partfun1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_funct_1(esk6_4(esk1_0,esk2_0,X1,esk4_0))
    | ~ r1_partfun1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_7]),c_0_8])])).

cnf(c_0_17,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_partfun1(esk6_4(esk1_0,esk2_0,X1,esk4_0),esk1_0)
    | ~ r1_partfun1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_7]),c_0_8])])).

cnf(c_0_18,plain,
    ( r1_partfun1(X1,esk6_4(X2,X3,X4,X1))
    | X3 = k1_xboole_0
    | ~ r1_partfun1(X4,X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,plain,
    ( r1_partfun1(X1,esk6_4(X2,X3,X1,X4))
    | X3 = k1_xboole_0
    | ~ r1_partfun1(X1,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | m1_subset_1(esk6_4(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_22,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_funct_1(esk6_4(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_23,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_partfun1(esk6_4(esk1_0,esk2_0,esk3_0,esk4_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_24,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_partfun1(X1,esk6_4(esk1_0,esk2_0,esk3_0,X1))
    | ~ r1_partfun1(esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_13]),c_0_15])])).

cnf(c_0_25,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_partfun1(X1,esk6_4(esk1_0,esk2_0,X1,esk4_0))
    | ~ r1_partfun1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_7]),c_0_8])])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ r1_partfun1(esk3_0,X1)
    | ~ r1_partfun1(esk4_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_27,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_funct_2(esk6_4(esk1_0,esk2_0,esk3_0,esk4_0),esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_partfun1(esk4_0,esk6_4(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_7]),c_0_14]),c_0_8])])).

cnf(c_0_29,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_partfun1(esk3_0,esk6_4(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_30,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_31,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_22]),c_0_21]),c_0_28]),c_0_29])).

cnf(c_0_32,plain,
    ( m1_subset_1(esk6_4(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X1 != k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_33,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])])).

cnf(c_0_34,plain,
    ( v1_partfun1(esk6_4(X1,X2,X3,X4),X1)
    | X1 != k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_35,plain,
    ( v1_funct_1(esk6_4(X1,X2,X3,X4))
    | X1 != k1_xboole_0
    | ~ r1_partfun1(X3,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk6_4(k1_xboole_0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_partfun1(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_31]),c_0_33])).

cnf(c_0_38,plain,
    ( v1_partfun1(esk6_4(k1_xboole_0,X1,X2,X3),k1_xboole_0)
    | ~ r1_partfun1(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( v1_funct_1(esk6_4(k1_xboole_0,X1,X2,X3))
    | ~ r1_partfun1(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( r1_partfun1(X1,esk6_4(X2,X3,X1,X4))
    | X2 != k1_xboole_0
    | ~ r1_partfun1(X1,X4)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_41,plain,
    ( r1_partfun1(X1,esk6_4(X2,X3,X4,X1))
    | X2 != k1_xboole_0
    | ~ r1_partfun1(X4,X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk6_4(k1_xboole_0,k1_xboole_0,X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ r1_partfun1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_8])])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_31]),c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( v1_partfun1(esk6_4(k1_xboole_0,k1_xboole_0,X1,esk4_0),k1_xboole_0)
    | ~ r1_partfun1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_37]),c_0_8])])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk6_4(k1_xboole_0,k1_xboole_0,X1,esk4_0))
    | ~ r1_partfun1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_37]),c_0_8])])).

cnf(c_0_46,plain,
    ( r1_partfun1(X1,esk6_4(k1_xboole_0,X2,X1,X3))
    | ~ r1_partfun1(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r1_partfun1(X1,esk6_4(k1_xboole_0,X2,X3,X1))
    | ~ r1_partfun1(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk6_4(k1_xboole_0,k1_xboole_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_14]),c_0_15])])).

cnf(c_0_49,negated_conjecture,
    ( v1_partfun1(esk6_4(k1_xboole_0,k1_xboole_0,esk3_0,esk4_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_43]),c_0_14]),c_0_15])])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_1(esk6_4(k1_xboole_0,k1_xboole_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_43]),c_0_14]),c_0_15])])).

cnf(c_0_51,negated_conjecture,
    ( r1_partfun1(X1,esk6_4(k1_xboole_0,k1_xboole_0,X1,esk4_0))
    | ~ r1_partfun1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_37]),c_0_8])])).

cnf(c_0_52,negated_conjecture,
    ( r1_partfun1(X1,esk6_4(k1_xboole_0,k1_xboole_0,esk3_0,X1))
    | ~ r1_partfun1(esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_43]),c_0_15])])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_xboole_0,k1_xboole_0)
    | ~ r1_partfun1(esk3_0,X1)
    | ~ r1_partfun1(esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_31]),c_0_31]),c_0_33]),c_0_33])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_2(esk6_4(k1_xboole_0,k1_xboole_0,esk3_0,esk4_0),k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_55,negated_conjecture,
    ( r1_partfun1(esk3_0,esk6_4(k1_xboole_0,k1_xboole_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_43]),c_0_14]),c_0_15])])).

cnf(c_0_56,negated_conjecture,
    ( r1_partfun1(esk4_0,esk6_4(k1_xboole_0,k1_xboole_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_37]),c_0_14]),c_0_8])])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56]),c_0_48]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
