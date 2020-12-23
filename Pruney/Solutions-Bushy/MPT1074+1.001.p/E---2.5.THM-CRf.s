%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1074+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:41 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 100 expanded)
%              Number of clauses        :   24 (  39 expanded)
%              Number of leaves         :    4 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 547 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t191_funct_2,conjecture,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ~ v1_xboole_0(X3)
         => ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_funct_2(X4,X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
             => ( ! [X5] :
                    ( m1_subset_1(X5,X2)
                   => r2_hidden(k3_funct_2(X2,X3,X4,X5),X1) )
               => r1_tarski(k2_relset_1(X2,X3,X4),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

fof(t190_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X2,X3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
     => ~ ( r2_hidden(X1,k2_relset_1(X2,X3,X4))
          & ! [X5] :
              ( m1_subset_1(X5,X2)
             => X1 != k1_funct_1(X4,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ~ v1_xboole_0(X3)
           => ! [X4] :
                ( ( v1_funct_1(X4)
                  & v1_funct_2(X4,X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
               => ( ! [X5] :
                      ( m1_subset_1(X5,X2)
                     => r2_hidden(k3_funct_2(X2,X3,X4,X5),X1) )
                 => r1_tarski(k2_relset_1(X2,X3,X4),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t191_funct_2])).

fof(c_0_5,plain,(
    ! [X16,X17,X18,X19] :
      ( ( m1_subset_1(esk2_4(X16,X17,X18,X19),X17)
        | ~ r2_hidden(X16,k2_relset_1(X17,X18,X19))
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( X16 = k1_funct_1(X19,esk2_4(X16,X17,X18,X19))
        | ~ r2_hidden(X16,k2_relset_1(X17,X18,X19))
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t190_funct_2])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X25] :
      ( ~ v1_xboole_0(esk4_0)
      & ~ v1_xboole_0(esk5_0)
      & v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,esk4_0,esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & ( ~ m1_subset_1(X25,esk4_0)
        | r2_hidden(k3_funct_2(esk4_0,esk5_0,esk6_0,X25),esk3_0) )
      & ~ r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),esk3_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).

cnf(c_0_7,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X1,k2_relset_1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X12,X13,X14,X15] :
      ( v1_xboole_0(X12)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,X12,X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | ~ m1_subset_1(X15,X12)
      | k3_funct_2(X12,X13,X14,X15) = k1_funct_1(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk2_4(X1,X2,X3,esk6_0),X2)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_2(esk6_0,X2,X3)
    | ~ r2_hidden(X1,k2_relset_1(X2,X3,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_13,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_14,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk2_4(X1,esk4_0,esk5_0,esk6_0),esk4_0)
    | ~ r2_hidden(X1,k2_relset_1(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( k3_funct_2(X1,X2,esk6_0,X3) = k1_funct_1(esk6_0,X3)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,X1)
    | ~ v1_funct_2(esk6_0,X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0,esk6_0),esk4_0)
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( X1 = k1_funct_1(X2,esk2_4(X1,X3,X4,X2))
    | ~ r2_hidden(X1,k2_relset_1(X3,X4,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k3_funct_2(esk4_0,esk5_0,esk6_0,X1),esk3_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( k3_funct_2(esk4_0,X1,esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X2),esk4_0,esk5_0,esk6_0)) = k1_funct_1(esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X2),esk4_0,esk5_0,esk6_0))
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X2)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ v1_funct_2(esk6_0,esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( k1_funct_1(esk6_0,esk2_4(X1,X2,X3,esk6_0)) = X1
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_2(esk6_0,X2,X3)
    | ~ r2_hidden(X1,k2_relset_1(X2,X3,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k3_funct_2(esk4_0,esk5_0,esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0,esk6_0)),esk3_0)
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k3_funct_2(esk4_0,esk5_0,esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0,esk6_0)) = k1_funct_1(esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0,esk6_0))
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_11]),c_0_12])])).

cnf(c_0_26,negated_conjecture,
    ( k1_funct_1(esk6_0,esk2_4(X1,esk4_0,esk5_0,esk6_0)) = X1
    | ~ r2_hidden(X1,k2_relset_1(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_11]),c_0_12])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0,esk6_0)),esk3_0)
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(esk6_0,esk2_4(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk4_0,esk5_0,esk6_0)) = esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1)
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relset_1(esk4_0,esk5_0,esk6_0),X1),esk3_0)
    | r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(esk4_0,esk5_0,esk6_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),
    [proof]).

%------------------------------------------------------------------------------
