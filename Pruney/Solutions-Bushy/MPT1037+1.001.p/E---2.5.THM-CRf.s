%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1037+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:37 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   50 (2893 expanded)
%              Number of clauses        :   43 (1021 expanded)
%              Number of leaves         :    3 ( 699 expanded)
%              Depth                    :   18
%              Number of atoms          :  283 (24105 expanded)
%              Number of equality atoms :   67 (6404 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   50 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t148_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ~ ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
          & ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_funct_2(X4,X1,X2)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ~ r1_partfun1(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_2)).

fof(t136_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ~ ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
          & ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_funct_2(X4,X1,X2)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ? [X5] :
                  ( r2_hidden(X5,k1_relset_1(X1,X2,X3))
                  & k1_funct_1(X4,X5) != k1_funct_1(X3,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_funct_2)).

fof(t145_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ( X2 = k1_xboole_0
             => X1 = k1_xboole_0 )
           => ( r1_partfun1(X3,X4)
            <=> ! [X5] :
                  ( r2_hidden(X5,k1_relset_1(X1,X2,X3))
                 => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_2)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ~ ( ( X2 = k1_xboole_0
             => X1 = k1_xboole_0 )
            & ! [X4] :
                ( ( v1_funct_1(X4)
                  & v1_funct_2(X4,X1,X2)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
               => ~ r1_partfun1(X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t148_funct_2])).

fof(c_0_4,plain,(
    ! [X6,X7,X8,X10] :
      ( ( v1_funct_1(esk1_3(X6,X7,X8))
        | X7 = k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( v1_funct_2(esk1_3(X6,X7,X8),X6,X7)
        | X7 = k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( m1_subset_1(esk1_3(X6,X7,X8),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | X7 = k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( ~ r2_hidden(X10,k1_relset_1(X6,X7,X8))
        | k1_funct_1(esk1_3(X6,X7,X8),X10) = k1_funct_1(X8,X10)
        | X7 = k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( v1_funct_1(esk1_3(X6,X7,X8))
        | X6 != k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( v1_funct_2(esk1_3(X6,X7,X8),X6,X7)
        | X6 != k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( m1_subset_1(esk1_3(X6,X7,X8),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | X6 != k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( ~ r2_hidden(X10,k1_relset_1(X6,X7,X8))
        | k1_funct_1(esk1_3(X6,X7,X8),X10) = k1_funct_1(X8,X10)
        | X6 != k1_xboole_0
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t136_funct_2])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X20] :
      ( v1_funct_1(esk5_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
      & ( esk4_0 != k1_xboole_0
        | esk3_0 = k1_xboole_0 )
      & ( ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,esk3_0,esk4_0)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
        | ~ r1_partfun1(esk5_0,X20) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])).

fof(c_0_6,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_partfun1(X13,X14)
        | ~ r2_hidden(X15,k1_relset_1(X11,X12,X13))
        | k1_funct_1(X13,X15) = k1_funct_1(X14,X15)
        | X12 = k1_xboole_0
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_1(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( r2_hidden(esk2_4(X11,X12,X13,X14),k1_relset_1(X11,X12,X13))
        | r1_partfun1(X13,X14)
        | X12 = k1_xboole_0
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_1(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( k1_funct_1(X13,esk2_4(X11,X12,X13,X14)) != k1_funct_1(X14,esk2_4(X11,X12,X13,X14))
        | r1_partfun1(X13,X14)
        | X12 = k1_xboole_0
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_1(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( ~ r1_partfun1(X13,X14)
        | ~ r2_hidden(X15,k1_relset_1(X11,X12,X13))
        | k1_funct_1(X13,X15) = k1_funct_1(X14,X15)
        | X11 != k1_xboole_0
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_1(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( r2_hidden(esk2_4(X11,X12,X13,X14),k1_relset_1(X11,X12,X13))
        | r1_partfun1(X13,X14)
        | X11 != k1_xboole_0
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_1(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( k1_funct_1(X13,esk2_4(X11,X12,X13,X14)) != k1_funct_1(X14,esk2_4(X11,X12,X13,X14))
        | r1_partfun1(X13,X14)
        | X11 != k1_xboole_0
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_1(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_2])])])])])).

cnf(c_0_7,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X2 = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( v1_funct_1(esk1_3(X1,X2,X3))
    | X2 = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,plain,
    ( v1_funct_2(esk1_3(X1,X2,X3),X1,X2)
    | X2 = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),k1_relset_1(X1,X2,X3))
    | r1_partfun1(X3,X4)
    | X2 = k1_xboole_0
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_14,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_1(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_8]),c_0_9])])).

cnf(c_0_15,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_2(esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_8]),c_0_9])])).

cnf(c_0_16,plain,
    ( k1_funct_1(esk1_3(X2,X3,X4),X1) = k1_funct_1(X4,X1)
    | X3 = k1_xboole_0
    | ~ r2_hidden(X1,k1_relset_1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_partfun1(X1,esk1_3(esk3_0,esk4_0,esk5_0))
    | r2_hidden(esk2_4(esk3_0,esk4_0,X1,esk1_3(esk3_0,esk4_0,esk5_0)),k1_relset_1(esk3_0,esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])).

cnf(c_0_18,plain,
    ( r1_partfun1(X1,X4)
    | X3 = k1_xboole_0
    | k1_funct_1(X1,esk2_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk2_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( k1_funct_1(esk1_3(esk3_0,esk4_0,esk5_0),X1) = k1_funct_1(esk5_0,X1)
    | esk4_0 = k1_xboole_0
    | ~ r2_hidden(X1,k1_relset_1(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_8]),c_0_9])])).

cnf(c_0_20,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_partfun1(esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | r2_hidden(esk2_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk4_0,esk5_0)),k1_relset_1(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_8]),c_0_9])])).

cnf(c_0_21,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_partfun1(X1,esk1_3(esk3_0,esk4_0,esk5_0))
    | k1_funct_1(X1,esk2_4(esk3_0,esk4_0,X1,esk1_3(esk3_0,esk4_0,esk5_0))) != k1_funct_1(esk1_3(esk3_0,esk4_0,esk5_0),esk2_4(esk3_0,esk4_0,X1,esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_13]),c_0_14]),c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( k1_funct_1(esk1_3(esk3_0,esk4_0,esk5_0),esk2_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))) = k1_funct_1(esk5_0,esk2_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk4_0,esk5_0)))
    | esk4_0 = k1_xboole_0
    | r1_partfun1(esk5_0,esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,esk3_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ r1_partfun1(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_partfun1(esk5_0,esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_8]),c_0_9])]),c_0_22])).

cnf(c_0_25,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),k1_relset_1(X1,X2,X3))
    | r1_partfun1(X3,X4)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_27,plain,
    ( v1_funct_1(esk1_3(X1,X2,X3))
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_28,plain,
    ( v1_funct_2(esk1_3(X1,X2,X3),X1,X2)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_29,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_30,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_14]),c_0_13]),c_0_15])).

cnf(c_0_31,plain,
    ( r1_partfun1(X1,X2)
    | r2_hidden(esk2_4(k1_xboole_0,X3,X1,X2),k1_relset_1(k1_xboole_0,X3,X1))
    | ~ v1_funct_2(X2,k1_xboole_0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( m1_subset_1(esk1_3(k1_xboole_0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( v1_funct_1(esk1_3(k1_xboole_0,X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( v1_funct_2(esk1_3(k1_xboole_0,X1,X2),k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_36,plain,
    ( r1_partfun1(X1,esk1_3(k1_xboole_0,X2,X3))
    | r2_hidden(esk2_4(k1_xboole_0,X2,X1,esk1_3(k1_xboole_0,X2,X3)),k1_relset_1(k1_xboole_0,X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8,c_0_30]),c_0_35])).

cnf(c_0_38,plain,
    ( k1_funct_1(esk1_3(X2,X3,X4),X1) = k1_funct_1(X4,X1)
    | ~ r2_hidden(X1,k1_relset_1(X2,X3,X4))
    | X2 != k1_xboole_0
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_39,negated_conjecture,
    ( r1_partfun1(esk5_0,esk1_3(k1_xboole_0,k1_xboole_0,X1))
    | r2_hidden(esk2_4(k1_xboole_0,k1_xboole_0,esk5_0,esk1_3(k1_xboole_0,k1_xboole_0,X1)),k1_relset_1(k1_xboole_0,k1_xboole_0,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_9])])).

cnf(c_0_40,plain,
    ( r1_partfun1(X1,X4)
    | k1_funct_1(X1,esk2_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk2_4(X2,X3,X1,X4))
    | X2 != k1_xboole_0
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_41,plain,
    ( k1_funct_1(esk1_3(k1_xboole_0,X1,X2),X3) = k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relset_1(k1_xboole_0,X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r1_partfun1(esk5_0,esk1_3(k1_xboole_0,k1_xboole_0,esk5_0))
    | r2_hidden(esk2_4(k1_xboole_0,k1_xboole_0,esk5_0,esk1_3(k1_xboole_0,k1_xboole_0,esk5_0)),k1_relset_1(k1_xboole_0,k1_xboole_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_37]),c_0_9])])).

cnf(c_0_43,plain,
    ( r1_partfun1(X1,X2)
    | k1_funct_1(X1,esk2_4(k1_xboole_0,X3,X1,X2)) != k1_funct_1(X2,esk2_4(k1_xboole_0,X3,X1,X2))
    | ~ v1_funct_2(X2,k1_xboole_0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( k1_funct_1(esk1_3(k1_xboole_0,k1_xboole_0,esk5_0),esk2_4(k1_xboole_0,k1_xboole_0,esk5_0,esk1_3(k1_xboole_0,k1_xboole_0,esk5_0))) = k1_funct_1(esk5_0,esk2_4(k1_xboole_0,k1_xboole_0,esk5_0,esk1_3(k1_xboole_0,k1_xboole_0,esk5_0)))
    | r1_partfun1(esk5_0,esk1_3(k1_xboole_0,k1_xboole_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_37]),c_0_9])])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_partfun1(esk5_0,X1)
    | ~ v1_funct_2(X1,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_30]),c_0_30]),c_0_35]),c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_funct_2(esk1_3(k1_xboole_0,k1_xboole_0,esk5_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(esk1_3(k1_xboole_0,k1_xboole_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(esk1_3(k1_xboole_0,k1_xboole_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_37]),c_0_9])]),c_0_45])).

cnf(c_0_47,negated_conjecture,
    ( ~ m1_subset_1(esk1_3(k1_xboole_0,k1_xboole_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(esk1_3(k1_xboole_0,k1_xboole_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_34]),c_0_37]),c_0_9])])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_funct_1(esk1_3(k1_xboole_0,k1_xboole_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_32]),c_0_37]),c_0_9])])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_33]),c_0_37]),c_0_9])]),
    [proof]).

%------------------------------------------------------------------------------
