%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:52 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 504 expanded)
%              Number of clauses        :   34 ( 162 expanded)
%              Number of leaves         :    2 ( 122 expanded)
%              Depth                    :   13
%              Number of atoms          :  258 (5494 expanded)
%              Number of equality atoms :   80 (1489 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   66 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t77_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X4,X1)
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
           => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

fof(t25_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => ( v2_funct_1(X3)
        <=> ! [X4,X5] :
              ( ( r2_hidden(X4,X1)
                & r2_hidden(X5,X1)
                & k1_funct_1(X3,X4) = k1_funct_1(X3,X5) )
             => X4 = X5 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_2)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( v2_funct_1(X2)
        <=> ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1)
                & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
             => X3 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_funct_2])).

fof(c_0_3,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ v2_funct_1(X8)
        | ~ r2_hidden(X9,X6)
        | ~ r2_hidden(X10,X6)
        | k1_funct_1(X8,X9) != k1_funct_1(X8,X10)
        | X9 = X10
        | X7 = k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( r2_hidden(esk1_3(X6,X7,X8),X6)
        | v2_funct_1(X8)
        | X7 = k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( r2_hidden(esk2_3(X6,X7,X8),X6)
        | v2_funct_1(X8)
        | X7 = k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( k1_funct_1(X8,esk1_3(X6,X7,X8)) = k1_funct_1(X8,esk2_3(X6,X7,X8))
        | v2_funct_1(X8)
        | X7 = k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( esk1_3(X6,X7,X8) != esk2_3(X6,X7,X8)
        | v2_funct_1(X8)
        | X7 = k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( ~ v2_funct_1(X8)
        | ~ r2_hidden(X9,X6)
        | ~ r2_hidden(X10,X6)
        | k1_funct_1(X8,X9) != k1_funct_1(X8,X10)
        | X9 = X10
        | X6 != k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( r2_hidden(esk1_3(X6,X7,X8),X6)
        | v2_funct_1(X8)
        | X6 != k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( r2_hidden(esk2_3(X6,X7,X8),X6)
        | v2_funct_1(X8)
        | X6 != k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( k1_funct_1(X8,esk1_3(X6,X7,X8)) = k1_funct_1(X8,esk2_3(X6,X7,X8))
        | v2_funct_1(X8)
        | X6 != k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( esk1_3(X6,X7,X8) != esk2_3(X6,X7,X8)
        | v2_funct_1(X8)
        | X6 != k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_funct_2])])])])])).

fof(c_0_4,negated_conjecture,(
    ! [X17,X18] :
      ( v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,esk3_0,esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
      & ( r2_hidden(esk5_0,esk3_0)
        | ~ v2_funct_1(esk4_0) )
      & ( r2_hidden(esk6_0,esk3_0)
        | ~ v2_funct_1(esk4_0) )
      & ( k1_funct_1(esk4_0,esk5_0) = k1_funct_1(esk4_0,esk6_0)
        | ~ v2_funct_1(esk4_0) )
      & ( esk5_0 != esk6_0
        | ~ v2_funct_1(esk4_0) )
      & ( v2_funct_1(esk4_0)
        | ~ r2_hidden(X17,esk3_0)
        | ~ r2_hidden(X18,esk3_0)
        | k1_funct_1(esk4_0,X17) != k1_funct_1(esk4_0,X18)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])])])).

cnf(c_0_5,plain,
    ( X2 = X4
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X4,X3)
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X4)
    | X3 != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X5))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( v1_funct_2(esk4_0,esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( v2_funct_1(esk4_0)
    | X1 = X2
    | ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X2,esk3_0)
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( X2 = X4
    | X5 = k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X4,X3)
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X5))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_11,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,X2)
    | esk3_0 != k1_xboole_0
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7]),c_0_8])]),c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,X2)
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_6]),c_0_7]),c_0_8])]),c_0_9]),c_0_11])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk6_0,esk3_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | v2_funct_1(X3)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_15,negated_conjecture,
    ( X1 = esk6_0
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,esk6_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_0) = k1_funct_1(esk4_0,esk6_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,negated_conjecture,
    ( esk5_0 != esk6_0
    | ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | v2_funct_1(X3)
    | X2 = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_20,negated_conjecture,
    ( X1 = esk2_3(esk3_0,X2,X3)
    | v2_funct_1(X3)
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,esk2_3(esk3_0,X2,X3))
    | esk3_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))
    | ~ v1_funct_2(X3,esk3_0,X2)
    | ~ v1_funct_1(X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_14])).

cnf(c_0_21,plain,
    ( k1_funct_1(X1,esk1_3(X2,X3,X1)) = k1_funct_1(X1,esk2_3(X2,X3,X1))
    | v2_funct_1(X1)
    | X2 != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_funct_1(esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( X1 = esk2_3(esk3_0,X2,X3)
    | X2 = k1_xboole_0
    | v2_funct_1(X3)
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,esk2_3(esk3_0,X2,X3))
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))
    | ~ v1_funct_2(X3,esk3_0,X2)
    | ~ v1_funct_1(X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_19])).

cnf(c_0_24,plain,
    ( k1_funct_1(X1,esk1_3(X2,X3,X1)) = k1_funct_1(X1,esk2_3(X2,X3,X1))
    | v2_funct_1(X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_25,negated_conjecture,
    ( X1 = esk2_3(esk3_0,X2,esk4_0)
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,esk1_3(esk3_0,X2,esk4_0))
    | esk3_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))
    | ~ v1_funct_2(esk4_0,esk3_0,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_8])]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( X1 = esk2_3(esk3_0,X2,esk4_0)
    | X2 = k1_xboole_0
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,esk1_3(esk3_0,X2,esk4_0))
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))
    | ~ v1_funct_2(esk4_0,esk3_0,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_8])]),c_0_22])).

cnf(c_0_27,plain,
    ( v2_funct_1(X3)
    | esk1_3(X1,X2,X3) != esk2_3(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_28,negated_conjecture,
    ( esk2_3(esk3_0,X1,esk4_0) = esk1_3(esk3_0,X1,esk4_0)
    | esk3_0 != k1_xboole_0
    | ~ r2_hidden(esk1_3(esk3_0,X1,esk4_0),esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ v1_funct_2(esk4_0,esk3_0,X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( v2_funct_1(X3)
    | X2 = k1_xboole_0
    | esk1_3(X1,X2,X3) != esk2_3(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_30,negated_conjecture,
    ( esk2_3(esk3_0,X1,esk4_0) = esk1_3(esk3_0,X1,esk4_0)
    | X1 = k1_xboole_0
    | ~ r2_hidden(esk1_3(esk3_0,X1,esk4_0),esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ v1_funct_2(esk4_0,esk3_0,X1) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ r2_hidden(esk1_3(esk3_0,X1,esk4_0),esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ v1_funct_2(esk4_0,esk3_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_8])]),c_0_22])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | v2_funct_1(X3)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk1_3(esk3_0,X1,esk4_0),esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ v1_funct_2(esk4_0,esk3_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_8])]),c_0_22])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | v2_funct_1(X3)
    | X2 = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_35,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ v1_funct_2(esk4_0,esk3_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_8])]),c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ v1_funct_2(esk4_0,esk3_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_8])]),c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_6]),c_0_7])])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_6]),c_0_7])]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:59:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.20/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.042 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t77_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(v2_funct_1(X2)<=>![X3, X4]:(((r2_hidden(X3,X1)&r2_hidden(X4,X1))&k1_funct_1(X2,X3)=k1_funct_1(X2,X4))=>X3=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 0.20/0.40  fof(t25_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v2_funct_1(X3)<=>![X4, X5]:(((r2_hidden(X4,X1)&r2_hidden(X5,X1))&k1_funct_1(X3,X4)=k1_funct_1(X3,X5))=>X4=X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_funct_2)).
% 0.20/0.40  fof(c_0_2, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(v2_funct_1(X2)<=>![X3, X4]:(((r2_hidden(X3,X1)&r2_hidden(X4,X1))&k1_funct_1(X2,X3)=k1_funct_1(X2,X4))=>X3=X4)))), inference(assume_negation,[status(cth)],[t77_funct_2])).
% 0.20/0.40  fof(c_0_3, plain, ![X6, X7, X8, X9, X10]:(((~v2_funct_1(X8)|(~r2_hidden(X9,X6)|~r2_hidden(X10,X6)|k1_funct_1(X8,X9)!=k1_funct_1(X8,X10)|X9=X10)|X7=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))))&((((r2_hidden(esk1_3(X6,X7,X8),X6)|v2_funct_1(X8)|X7=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))))&(r2_hidden(esk2_3(X6,X7,X8),X6)|v2_funct_1(X8)|X7=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))))&(k1_funct_1(X8,esk1_3(X6,X7,X8))=k1_funct_1(X8,esk2_3(X6,X7,X8))|v2_funct_1(X8)|X7=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))))&(esk1_3(X6,X7,X8)!=esk2_3(X6,X7,X8)|v2_funct_1(X8)|X7=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))))))&((~v2_funct_1(X8)|(~r2_hidden(X9,X6)|~r2_hidden(X10,X6)|k1_funct_1(X8,X9)!=k1_funct_1(X8,X10)|X9=X10)|X6!=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))))&((((r2_hidden(esk1_3(X6,X7,X8),X6)|v2_funct_1(X8)|X6!=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))))&(r2_hidden(esk2_3(X6,X7,X8),X6)|v2_funct_1(X8)|X6!=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))))&(k1_funct_1(X8,esk1_3(X6,X7,X8))=k1_funct_1(X8,esk2_3(X6,X7,X8))|v2_funct_1(X8)|X6!=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))))&(esk1_3(X6,X7,X8)!=esk2_3(X6,X7,X8)|v2_funct_1(X8)|X6!=k1_xboole_0|(~v1_funct_1(X8)|~v1_funct_2(X8,X6,X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_funct_2])])])])])).
% 0.20/0.40  fof(c_0_4, negated_conjecture, ![X17, X18]:(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk3_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))))&(((((r2_hidden(esk5_0,esk3_0)|~v2_funct_1(esk4_0))&(r2_hidden(esk6_0,esk3_0)|~v2_funct_1(esk4_0)))&(k1_funct_1(esk4_0,esk5_0)=k1_funct_1(esk4_0,esk6_0)|~v2_funct_1(esk4_0)))&(esk5_0!=esk6_0|~v2_funct_1(esk4_0)))&(v2_funct_1(esk4_0)|(~r2_hidden(X17,esk3_0)|~r2_hidden(X18,esk3_0)|k1_funct_1(esk4_0,X17)!=k1_funct_1(esk4_0,X18)|X17=X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])])])).
% 0.20/0.40  cnf(c_0_5, plain, (X2=X4|~v2_funct_1(X1)|~r2_hidden(X2,X3)|~r2_hidden(X4,X3)|k1_funct_1(X1,X2)!=k1_funct_1(X1,X4)|X3!=k1_xboole_0|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X5)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.40  cnf(c_0_6, negated_conjecture, (v1_funct_2(esk4_0,esk3_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.40  cnf(c_0_7, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.40  cnf(c_0_8, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.40  cnf(c_0_9, negated_conjecture, (v2_funct_1(esk4_0)|X1=X2|~r2_hidden(X1,esk3_0)|~r2_hidden(X2,esk3_0)|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.40  cnf(c_0_10, plain, (X2=X4|X5=k1_xboole_0|~v2_funct_1(X1)|~r2_hidden(X2,X3)|~r2_hidden(X4,X3)|k1_funct_1(X1,X2)!=k1_funct_1(X1,X4)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X5)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.40  cnf(c_0_11, negated_conjecture, (X1=X2|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,X2)|esk3_0!=k1_xboole_0|~r2_hidden(X2,esk3_0)|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_6]), c_0_7]), c_0_8])]), c_0_9])).
% 0.20/0.40  cnf(c_0_12, negated_conjecture, (X1=X2|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,X2)|~r2_hidden(X2,esk3_0)|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_6]), c_0_7]), c_0_8])]), c_0_9]), c_0_11])).
% 0.20/0.40  cnf(c_0_13, negated_conjecture, (r2_hidden(esk6_0,esk3_0)|~v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.40  cnf(c_0_14, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|v2_funct_1(X3)|X1!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.40  cnf(c_0_15, negated_conjecture, (X1=esk6_0|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,esk6_0)|~r2_hidden(X1,esk3_0)|~v2_funct_1(esk4_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.40  cnf(c_0_16, negated_conjecture, (r2_hidden(esk5_0,esk3_0)|~v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.40  cnf(c_0_17, negated_conjecture, (k1_funct_1(esk4_0,esk5_0)=k1_funct_1(esk4_0,esk6_0)|~v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.40  cnf(c_0_18, negated_conjecture, (esk5_0!=esk6_0|~v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.40  cnf(c_0_19, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|v2_funct_1(X3)|X2=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.40  cnf(c_0_20, negated_conjecture, (X1=esk2_3(esk3_0,X2,X3)|v2_funct_1(X3)|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,esk2_3(esk3_0,X2,X3))|esk3_0!=k1_xboole_0|~r2_hidden(X1,esk3_0)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))|~v1_funct_2(X3,esk3_0,X2)|~v1_funct_1(X3)), inference(spm,[status(thm)],[c_0_12, c_0_14])).
% 0.20/0.40  cnf(c_0_21, plain, (k1_funct_1(X1,esk1_3(X2,X3,X1))=k1_funct_1(X1,esk2_3(X2,X3,X1))|v2_funct_1(X1)|X2!=k1_xboole_0|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.40  cnf(c_0_22, negated_conjecture, (~v2_funct_1(esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])).
% 0.20/0.40  cnf(c_0_23, negated_conjecture, (X1=esk2_3(esk3_0,X2,X3)|X2=k1_xboole_0|v2_funct_1(X3)|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,esk2_3(esk3_0,X2,X3))|~r2_hidden(X1,esk3_0)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))|~v1_funct_2(X3,esk3_0,X2)|~v1_funct_1(X3)), inference(spm,[status(thm)],[c_0_12, c_0_19])).
% 0.20/0.40  cnf(c_0_24, plain, (k1_funct_1(X1,esk1_3(X2,X3,X1))=k1_funct_1(X1,esk2_3(X2,X3,X1))|v2_funct_1(X1)|X3=k1_xboole_0|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.40  cnf(c_0_25, negated_conjecture, (X1=esk2_3(esk3_0,X2,esk4_0)|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,esk1_3(esk3_0,X2,esk4_0))|esk3_0!=k1_xboole_0|~r2_hidden(X1,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))|~v1_funct_2(esk4_0,esk3_0,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_8])]), c_0_22])).
% 0.20/0.40  cnf(c_0_26, negated_conjecture, (X1=esk2_3(esk3_0,X2,esk4_0)|X2=k1_xboole_0|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,esk1_3(esk3_0,X2,esk4_0))|~r2_hidden(X1,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))|~v1_funct_2(esk4_0,esk3_0,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_8])]), c_0_22])).
% 0.20/0.40  cnf(c_0_27, plain, (v2_funct_1(X3)|esk1_3(X1,X2,X3)!=esk2_3(X1,X2,X3)|X1!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.40  cnf(c_0_28, negated_conjecture, (esk2_3(esk3_0,X1,esk4_0)=esk1_3(esk3_0,X1,esk4_0)|esk3_0!=k1_xboole_0|~r2_hidden(esk1_3(esk3_0,X1,esk4_0),esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~v1_funct_2(esk4_0,esk3_0,X1)), inference(er,[status(thm)],[c_0_25])).
% 0.20/0.40  cnf(c_0_29, plain, (v2_funct_1(X3)|X2=k1_xboole_0|esk1_3(X1,X2,X3)!=esk2_3(X1,X2,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.40  cnf(c_0_30, negated_conjecture, (esk2_3(esk3_0,X1,esk4_0)=esk1_3(esk3_0,X1,esk4_0)|X1=k1_xboole_0|~r2_hidden(esk1_3(esk3_0,X1,esk4_0),esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~v1_funct_2(esk4_0,esk3_0,X1)), inference(er,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_31, negated_conjecture, (esk3_0!=k1_xboole_0|~r2_hidden(esk1_3(esk3_0,X1,esk4_0),esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~v1_funct_2(esk4_0,esk3_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_8])]), c_0_22])).
% 0.20/0.40  cnf(c_0_32, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|v2_funct_1(X3)|X1!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (X1=k1_xboole_0|~r2_hidden(esk1_3(esk3_0,X1,esk4_0),esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~v1_funct_2(esk4_0,esk3_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_8])]), c_0_22])).
% 0.20/0.40  cnf(c_0_34, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|v2_funct_1(X3)|X2=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.40  cnf(c_0_35, negated_conjecture, (esk3_0!=k1_xboole_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~v1_funct_2(esk4_0,esk3_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_8])]), c_0_22])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (X1=k1_xboole_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~v1_funct_2(esk4_0,esk3_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_8])]), c_0_22])).
% 0.20/0.40  cnf(c_0_37, negated_conjecture, (esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_6]), c_0_7])])).
% 0.20/0.40  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_6]), c_0_7])]), c_0_37]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 39
% 0.20/0.40  # Proof object clause steps            : 34
% 0.20/0.40  # Proof object formula steps           : 5
% 0.20/0.40  # Proof object conjectures             : 27
% 0.20/0.40  # Proof object clause conjectures      : 24
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 18
% 0.20/0.40  # Proof object initial formulas used   : 2
% 0.20/0.40  # Proof object generating inferences   : 16
% 0.20/0.40  # Proof object simplifying inferences  : 34
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 2
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 18
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 18
% 0.20/0.40  # Processed clauses                    : 65
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 10
% 0.20/0.40  # ...remaining for further processing  : 55
% 0.20/0.40  # Other redundant clauses eliminated   : 0
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 9
% 0.20/0.40  # Backward-rewritten                   : 0
% 0.20/0.40  # Generated clauses                    : 75
% 0.20/0.40  # ...of the previous two non-trivial   : 64
% 0.20/0.40  # Contextual simplify-reflections      : 7
% 0.20/0.40  # Paramodulations                      : 70
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 5
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 28
% 0.20/0.40  #    Positive orientable unit clauses  : 3
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 2
% 0.20/0.40  #    Non-unit-clauses                  : 23
% 0.20/0.40  # Current number of unprocessed clauses: 20
% 0.20/0.40  # ...number of literals in the above   : 177
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 27
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 457
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 64
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 17
% 0.20/0.40  # Unit Clause-clause subsumption calls : 15
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 0
% 0.20/0.40  # BW rewrite match successes           : 0
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 4290
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.054 s
% 0.20/0.40  # System time              : 0.003 s
% 0.20/0.40  # Total time               : 0.057 s
% 0.20/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
