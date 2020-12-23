%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0717+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:05 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  87 expanded)
%              Number of clauses        :   22 (  36 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  128 ( 357 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t172_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v5_relat_1(X2,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( r2_hidden(X3,k1_relat_1(X2))
           => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t172_funct_1])).

fof(c_0_8,plain,(
    ! [X5,X6] :
      ( ( ~ v5_relat_1(X6,X5)
        | r1_tarski(k2_relat_1(X6),X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r1_tarski(k2_relat_1(X6),X5)
        | v5_relat_1(X6,X5)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v5_relat_1(esk5_0,esk4_0)
    & v1_funct_1(esk5_0)
    & r2_hidden(esk6_0,k1_relat_1(esk5_0))
    & ~ r2_hidden(k1_funct_1(esk5_0,esk6_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X7,X8,X9,X11,X12,X13,X15] :
      ( ( r2_hidden(esk1_3(X7,X8,X9),k1_relat_1(X7))
        | ~ r2_hidden(X9,X8)
        | X8 != k2_relat_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( X9 = k1_funct_1(X7,esk1_3(X7,X8,X9))
        | ~ r2_hidden(X9,X8)
        | X8 != k2_relat_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( ~ r2_hidden(X12,k1_relat_1(X7))
        | X11 != k1_funct_1(X7,X12)
        | r2_hidden(X11,X8)
        | X8 != k2_relat_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( ~ r2_hidden(esk2_2(X7,X13),X13)
        | ~ r2_hidden(X15,k1_relat_1(X7))
        | esk2_2(X7,X13) != k1_funct_1(X7,X15)
        | X13 = k2_relat_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( r2_hidden(esk3_2(X7,X13),k1_relat_1(X7))
        | r2_hidden(esk2_2(X7,X13),X13)
        | X13 = k2_relat_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( esk2_2(X7,X13) = k1_funct_1(X7,esk3_2(X7,X13))
        | r2_hidden(esk2_2(X7,X13),X13)
        | X13 = k2_relat_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_11,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_12,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v5_relat_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | m1_subset_1(X21,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_19,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_15])])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk5_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,X1),k2_relat_1(esk5_0))
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_14])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_25,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,X18)
      | v1_xboole_0(X18)
      | r2_hidden(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(X1,esk4_0)
    | ~ r2_hidden(X1,k2_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk6_0),k2_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_28,plain,(
    ! [X24,X25,X26] :
      ( ~ r2_hidden(X24,X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X26))
      | ~ v1_xboole_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_29,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k1_funct_1(esk5_0,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk5_0,esk6_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_27,c_0_35]),
    [proof]).

%------------------------------------------------------------------------------
