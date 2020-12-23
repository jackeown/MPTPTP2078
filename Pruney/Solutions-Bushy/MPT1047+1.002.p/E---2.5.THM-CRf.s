%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1047+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:38 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 741 expanded)
%              Number of clauses        :   63 ( 296 expanded)
%              Number of leaves         :   11 ( 183 expanded)
%              Depth                    :   23
%              Number of atoms          :  465 (7924 expanded)
%              Number of equality atoms :   91 (1622 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   68 (   4 average)
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

fof(symmetry_r1_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_partfun1(X1,X2)
       => r1_partfun1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_partfun1)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(t143_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => r1_partfun1(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t66_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,k1_tarski(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,k1_tarski(X2))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => r2_relset_1(X1,k1_tarski(X2),X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_2)).

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

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,k1_tarski(X2))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
           => k5_partfun1(X1,k1_tarski(X2),X3) = k1_tarski(X4) ) ) ),
    inference(assume_negation,[status(cth)],[t164_funct_2])).

fof(c_0_12,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X37)
      | ~ v1_funct_1(X37)
      | ~ v1_relat_1(X38)
      | ~ v1_funct_1(X38)
      | ~ r1_partfun1(X37,X38)
      | r1_partfun1(X38,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_partfun1])])).

fof(c_0_13,plain,(
    ! [X20,X21,X22,X23,X24,X26,X27,X28,X30] :
      ( ( v1_funct_1(esk2_5(X20,X21,X22,X23,X24))
        | ~ r2_hidden(X24,X23)
        | X23 != k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( m1_subset_1(esk2_5(X20,X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ r2_hidden(X24,X23)
        | X23 != k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( esk2_5(X20,X21,X22,X23,X24) = X24
        | ~ r2_hidden(X24,X23)
        | X23 != k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( v1_partfun1(esk2_5(X20,X21,X22,X23,X24),X20)
        | ~ r2_hidden(X24,X23)
        | X23 != k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( r1_partfun1(X22,esk2_5(X20,X21,X22,X23,X24))
        | ~ r2_hidden(X24,X23)
        | X23 != k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | X27 != X26
        | ~ v1_partfun1(X27,X20)
        | ~ r1_partfun1(X22,X27)
        | r2_hidden(X26,X23)
        | X23 != k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( ~ r2_hidden(esk3_4(X20,X21,X22,X28),X28)
        | ~ v1_funct_1(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | X30 != esk3_4(X20,X21,X22,X28)
        | ~ v1_partfun1(X30,X20)
        | ~ r1_partfun1(X22,X30)
        | X28 = k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( v1_funct_1(esk4_4(X20,X21,X22,X28))
        | r2_hidden(esk3_4(X20,X21,X22,X28),X28)
        | X28 = k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( m1_subset_1(esk4_4(X20,X21,X22,X28),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | r2_hidden(esk3_4(X20,X21,X22,X28),X28)
        | X28 = k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( esk4_4(X20,X21,X22,X28) = esk3_4(X20,X21,X22,X28)
        | r2_hidden(esk3_4(X20,X21,X22,X28),X28)
        | X28 = k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( v1_partfun1(esk4_4(X20,X21,X22,X28),X20)
        | r2_hidden(esk3_4(X20,X21,X22,X28),X28)
        | X28 = k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( r1_partfun1(X22,esk4_4(X20,X21,X22,X28))
        | r2_hidden(esk3_4(X20,X21,X22,X28),X28)
        | X28 = k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

fof(c_0_14,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_15,plain,(
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

fof(c_0_16,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0))))
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk5_0,k1_tarski(esk6_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0))))
    & k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0) != k1_tarski(esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_17,plain,(
    ! [X32] : ~ v1_xboole_0(k1_tarski(X32)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_18,plain,
    ( r1_partfun1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r1_partfun1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r1_partfun1(X1,esk2_5(X2,X3,X1,X4,X5))
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X2,X3,X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v1_funct_1(esk2_5(X1,X2,X3,X4,X5))
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r2_hidden(X4,X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != X4
    | ~ v1_partfun1(X1,X2)
    | ~ r1_partfun1(X5,X1)
    | X6 != k5_partfun1(X2,X3,X5)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,k1_tarski(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_28,plain,(
    ! [X39,X40,X41,X42] :
      ( ~ v1_funct_1(X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,k1_tarski(X40))))
      | ~ v1_funct_1(X42)
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,k1_tarski(X40))))
      | r1_partfun1(X41,X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_partfun1])])])).

cnf(c_0_29,plain,
    ( r1_partfun1(esk2_5(X1,X2,X3,X4,X5),X3)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ r2_hidden(X5,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(esk2_5(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_30,plain,
    ( esk2_5(X1,X2,X3,X4,X5) = X5
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | X2 != k5_partfun1(X3,X4,X5)
    | ~ r1_partfun1(X5,X1)
    | ~ v1_partfun1(X1,X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( v1_partfun1(esk8_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_33,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r1_partfun1(X1,X2)
    | X3 != k5_partfun1(X4,X5,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk8_0,X1)
    | X1 != k5_partfun1(esk5_0,k1_tarski(esk6_0),X2)
    | ~ r1_partfun1(X2,esk8_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_26]),c_0_32]),c_0_25])])).

cnf(c_0_36,negated_conjecture,
    ( r1_partfun1(X1,esk8_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_26]),c_0_25])])).

cnf(c_0_37,plain,
    ( r1_partfun1(X1,X2)
    | ~ r2_hidden(X1,k5_partfun1(X3,X4,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk8_0,k5_partfun1(esk5_0,k1_tarski(esk6_0),X1))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_35]),c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_26])).

cnf(c_0_40,plain,
    ( m1_subset_1(esk2_5(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,plain,
    ( v1_partfun1(esk2_5(X1,X2,X3,X4,X5),X1)
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( r1_partfun1(esk8_0,X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_43,plain,
    ( r2_hidden(esk2_5(X1,X2,X3,X4,X5),X6)
    | X6 != k5_partfun1(X1,X2,X7)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ r1_partfun1(X7,esk2_5(X1,X2,X3,X4,X5))
    | ~ r2_hidden(X5,X4)
    | ~ v1_funct_1(X7)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_40]),c_0_21]),c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r1_partfun1(esk8_0,esk2_5(esk5_0,k1_tarski(esk6_0),X1,X2,X3))
    | X2 != k5_partfun1(esk5_0,k1_tarski(esk6_0),X1)
    | ~ r2_hidden(X3,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_40]),c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_5(esk5_0,k1_tarski(esk6_0),X1,X2,X3),X4)
    | X4 != k5_partfun1(esk5_0,k1_tarski(esk6_0),esk8_0)
    | X2 != k5_partfun1(esk5_0,k1_tarski(esk6_0),X1)
    | ~ r2_hidden(X3,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_25]),c_0_26])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k5_partfun1(esk5_0,k1_tarski(esk6_0),esk8_0)
    | X3 != k5_partfun1(esk5_0,k1_tarski(esk6_0),X4)
    | ~ r2_hidden(X1,X3)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_30])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),esk8_0))
    | X2 != k5_partfun1(esk5_0,k1_tarski(esk6_0),X3)
    | ~ r2_hidden(X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(er,[status(thm)],[c_0_46])).

fof(c_0_48,plain,(
    ! [X33,X34,X35,X36] :
      ( ( ~ r2_relset_1(X33,X34,X35,X36)
        | X35 = X36
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( X35 != X36
        | r2_relset_1(X33,X34,X35,X36)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_49,plain,(
    ! [X51,X52,X53,X54] :
      ( ~ v1_funct_1(X53)
      | ~ v1_funct_2(X53,X51,k1_tarski(X52))
      | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,k1_tarski(X52))))
      | ~ v1_funct_1(X54)
      | ~ v1_funct_2(X54,X51,k1_tarski(X52))
      | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,k1_tarski(X52))))
      | r2_relset_1(X51,k1_tarski(X52),X53,X54) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_funct_2])])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),esk8_0))
    | ~ r2_hidden(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),X2))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_51,plain,
    ( r1_partfun1(X1,esk2_5(X2,k1_tarski(X3),X4,X5,X6))
    | X5 != k5_partfun1(X2,k1_tarski(X3),X4)
    | ~ r2_hidden(X6,X5)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_40]),c_0_21])).

cnf(c_0_52,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,plain,
    ( r2_relset_1(X2,k1_tarski(X3),X1,X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,k1_tarski(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,k1_tarski(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_54,plain,(
    ! [X43,X44,X45,X46] :
      ( ( v1_funct_1(X46)
        | ~ r2_hidden(X46,k5_partfun1(X43,X44,X45))
        | ~ v1_funct_1(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( v1_funct_2(X46,X43,X44)
        | ~ r2_hidden(X46,k5_partfun1(X43,X44,X45))
        | ~ v1_funct_1(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | ~ r2_hidden(X46,k5_partfun1(X43,X44,X45))
        | ~ v1_funct_1(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk2_5(esk5_0,k1_tarski(esk6_0),X1,X2,X3),k5_partfun1(esk5_0,k1_tarski(esk6_0),esk8_0))
    | k5_partfun1(esk5_0,k1_tarski(esk6_0),X4) != k5_partfun1(esk5_0,k1_tarski(esk6_0),esk8_0)
    | X2 != k5_partfun1(esk5_0,k1_tarski(esk6_0),X1)
    | ~ r2_hidden(X3,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_45])).

cnf(c_0_56,plain,
    ( r1_partfun1(X1,X2)
    | X3 != k5_partfun1(X4,k1_tarski(X5),X6)
    | ~ r2_hidden(X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,k1_tarski(X5))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,k1_tarski(X5)))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_30])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ v1_funct_2(X2,X3,k1_tarski(X4))
    | ~ v1_funct_2(X1,X3,k1_tarski(X4))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,k1_tarski(X4))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,k1_tarski(X4)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk2_5(esk5_0,k1_tarski(esk6_0),X1,X2,X3),k5_partfun1(esk5_0,k1_tarski(esk6_0),esk8_0))
    | X2 != k5_partfun1(esk5_0,k1_tarski(esk6_0),X1)
    | ~ r2_hidden(X3,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_55]),c_0_25]),c_0_26])])).

cnf(c_0_62,negated_conjecture,
    ( r1_partfun1(esk7_0,X1)
    | X2 != k5_partfun1(esk5_0,k1_tarski(esk6_0),X3)
    | ~ r2_hidden(X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_63,negated_conjecture,
    ( X1 = esk8_0
    | ~ v1_funct_2(X1,esk5_0,k1_tarski(esk6_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_2(esk2_5(esk5_0,k1_tarski(esk6_0),X1,X2,X3),esk5_0,k1_tarski(esk6_0))
    | X2 != k5_partfun1(esk5_0,k1_tarski(esk6_0),X1)
    | ~ r2_hidden(X3,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_25]),c_0_26])])).

cnf(c_0_65,negated_conjecture,
    ( r1_partfun1(esk7_0,X1)
    | ~ r2_hidden(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),X2))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( esk2_5(esk5_0,k1_tarski(esk6_0),X1,X2,X3) = esk8_0
    | X2 != k5_partfun1(esk5_0,k1_tarski(esk6_0),X1)
    | ~ r2_hidden(X3,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_40]),c_0_21])).

cnf(c_0_67,negated_conjecture,
    ( r1_partfun1(esk7_0,esk2_5(esk5_0,k1_tarski(esk6_0),X1,X2,X3))
    | X2 != k5_partfun1(esk5_0,k1_tarski(esk6_0),X1)
    | ~ r2_hidden(X3,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_61]),c_0_25]),c_0_26])])).

cnf(c_0_68,negated_conjecture,
    ( esk8_0 = X1
    | X2 != k5_partfun1(esk5_0,k1_tarski(esk6_0),X3)
    | ~ r2_hidden(X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_66])).

fof(c_0_69,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X13
        | X14 != k1_tarski(X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_tarski(X13) )
      & ( ~ r2_hidden(esk1_2(X17,X18),X18)
        | esk1_2(X17,X18) != X17
        | X18 = k1_tarski(X17) )
      & ( r2_hidden(esk1_2(X17,X18),X18)
        | esk1_2(X17,X18) = X17
        | X18 = k1_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk2_5(esk5_0,k1_tarski(esk6_0),X1,X2,X3),X4)
    | X4 != k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0)
    | X2 != k5_partfun1(esk5_0,k1_tarski(esk6_0),X1)
    | ~ r2_hidden(X3,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_67]),c_0_58]),c_0_57])])).

cnf(c_0_71,negated_conjecture,
    ( esk8_0 = X1
    | ~ r2_hidden(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),X2))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_72,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0)
    | X3 != k5_partfun1(esk5_0,k1_tarski(esk6_0),X4)
    | ~ r2_hidden(X1,X3)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_30])).

cnf(c_0_74,negated_conjecture,
    ( esk1_2(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),X2)) = esk8_0
    | esk1_2(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),X2)) = X1
    | k5_partfun1(esk5_0,k1_tarski(esk6_0),X2) = k1_tarski(X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0))
    | X2 != k5_partfun1(esk5_0,k1_tarski(esk6_0),X3)
    | ~ r2_hidden(X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk8_0,k5_partfun1(esk5_0,k1_tarski(esk6_0),esk8_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_38])).

cnf(c_0_77,negated_conjecture,
    ( esk1_2(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0)) = esk8_0
    | esk1_2(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0)) = X1
    | k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0) = k1_tarski(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_57]),c_0_58])])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0))
    | ~ r2_hidden(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),X2))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk8_0,k5_partfun1(esk5_0,k1_tarski(esk6_0),esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_26]),c_0_25])])).

cnf(c_0_80,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_81,negated_conjecture,
    ( esk1_2(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0)) = esk8_0
    | k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0) = k1_tarski(X1)
    | X1 != esk8_0 ),
    inference(ef,[status(thm)],[c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk8_0,k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_25]),c_0_26])])).

cnf(c_0_83,negated_conjecture,
    ( k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0) = k1_tarski(X1)
    | esk8_0 != X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])])).

cnf(c_0_84,negated_conjecture,
    ( k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0) != k1_tarski(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_83]),c_0_84]),
    [proof]).

%------------------------------------------------------------------------------
