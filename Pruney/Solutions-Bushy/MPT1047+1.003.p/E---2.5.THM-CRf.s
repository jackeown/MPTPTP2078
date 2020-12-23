%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1047+1.003 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 720 expanded)
%              Number of clauses        :   52 ( 282 expanded)
%              Number of leaves         :    9 ( 175 expanded)
%              Depth                    :   15
%              Number of atoms          :  364 (4203 expanded)
%              Number of equality atoms :   91 ( 948 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   68 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_2)).

fof(t164_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,k1_tarski(X2))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => k5_partfun1(X1,k1_tarski(X2),X3) = k1_tarski(X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_2)).

fof(t158_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
         => ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

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

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(t143_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => r1_partfun1(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_partfun1)).

fof(c_0_9,plain,(
    ! [X30,X31,X32,X33] :
      ( ( ~ r2_relset_1(X30,X31,X32,X33)
        | X32 = X33
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( X32 != X33
        | r2_relset_1(X30,X31,X32,X33)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_10,plain,(
    ! [X44,X45,X46,X47] :
      ( ~ v1_funct_1(X46)
      | ~ v1_funct_2(X46,X44,k1_tarski(X45))
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,k1_tarski(X45))))
      | ~ v1_funct_1(X47)
      | ~ v1_funct_2(X47,X44,k1_tarski(X45))
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,k1_tarski(X45))))
      | r2_relset_1(X44,k1_tarski(X45),X46,X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_funct_2])])])).

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

cnf(c_0_12,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_relset_1(X2,k1_tarski(X3),X1,X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,k1_tarski(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,k1_tarski(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0))))
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk5_0,k1_tarski(esk6_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0))))
    & k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0) != k1_tarski(esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_15,plain,(
    ! [X38,X39,X40,X41] :
      ( ( v1_funct_1(X41)
        | ~ r2_hidden(X41,k5_partfun1(X38,X39,X40))
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( v1_funct_2(X41,X38,X39)
        | ~ r2_hidden(X41,k5_partfun1(X38,X39,X40))
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | ~ r2_hidden(X41,k5_partfun1(X38,X39,X40))
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).

fof(c_0_16,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X10
        | X11 != k1_tarski(X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k1_tarski(X10) )
      & ( ~ r2_hidden(esk1_2(X14,X15),X15)
        | esk1_2(X14,X15) != X14
        | X15 = k1_tarski(X14) )
      & ( r2_hidden(esk1_2(X14,X15),X15)
        | esk1_2(X14,X15) = X14
        | X15 = k1_tarski(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_17,plain,
    ( X1 = X2
    | ~ v1_funct_2(X2,X3,k1_tarski(X4))
    | ~ v1_funct_2(X1,X3,k1_tarski(X4))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,k1_tarski(X4))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,k1_tarski(X4)))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,k1_tarski(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( X1 = esk8_0
    | ~ v1_funct_2(X1,esk5_0,k1_tarski(esk6_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_26,plain,
    ( esk1_2(X1,k5_partfun1(X2,X3,X4)) = X1
    | k5_partfun1(X2,X3,X4) = k1_tarski(X1)
    | v1_funct_2(esk1_2(X1,k5_partfun1(X2,X3,X4)),X2,X3)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( esk1_2(X1,k5_partfun1(X2,X3,X4)) = X1
    | k5_partfun1(X2,X3,X4) = k1_tarski(X1)
    | m1_subset_1(esk1_2(X1,k5_partfun1(X2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_28,plain,
    ( esk1_2(X1,k5_partfun1(X2,X3,X4)) = X1
    | k5_partfun1(X2,X3,X4) = k1_tarski(X1)
    | v1_funct_1(esk1_2(X1,k5_partfun1(X2,X3,X4)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

fof(c_0_29,plain,(
    ! [X17,X18,X19,X20,X21,X23,X24,X25,X27] :
      ( ( v1_funct_1(esk2_5(X17,X18,X19,X20,X21))
        | ~ r2_hidden(X21,X20)
        | X20 != k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( m1_subset_1(esk2_5(X17,X18,X19,X20,X21),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ r2_hidden(X21,X20)
        | X20 != k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( esk2_5(X17,X18,X19,X20,X21) = X21
        | ~ r2_hidden(X21,X20)
        | X20 != k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v1_partfun1(esk2_5(X17,X18,X19,X20,X21),X17)
        | ~ r2_hidden(X21,X20)
        | X20 != k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( r1_partfun1(X19,esk2_5(X17,X18,X19,X20,X21))
        | ~ r2_hidden(X21,X20)
        | X20 != k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | X24 != X23
        | ~ v1_partfun1(X24,X17)
        | ~ r1_partfun1(X19,X24)
        | r2_hidden(X23,X20)
        | X20 != k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( ~ r2_hidden(esk3_4(X17,X18,X19,X25),X25)
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | X27 != esk3_4(X17,X18,X19,X25)
        | ~ v1_partfun1(X27,X17)
        | ~ r1_partfun1(X19,X27)
        | X25 = k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v1_funct_1(esk4_4(X17,X18,X19,X25))
        | r2_hidden(esk3_4(X17,X18,X19,X25),X25)
        | X25 = k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( m1_subset_1(esk4_4(X17,X18,X19,X25),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | r2_hidden(esk3_4(X17,X18,X19,X25),X25)
        | X25 = k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( esk4_4(X17,X18,X19,X25) = esk3_4(X17,X18,X19,X25)
        | r2_hidden(esk3_4(X17,X18,X19,X25),X25)
        | X25 = k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v1_partfun1(esk4_4(X17,X18,X19,X25),X17)
        | r2_hidden(esk3_4(X17,X18,X19,X25),X25)
        | X25 = k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( r1_partfun1(X19,esk4_4(X17,X18,X19,X25))
        | r2_hidden(esk3_4(X17,X18,X19,X25),X25)
        | X25 = k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

fof(c_0_30,plain,(
    ! [X7,X8,X9] :
      ( ( v1_funct_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | v1_xboole_0(X8) )
      & ( v1_partfun1(X9,X7)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | v1_xboole_0(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_31,plain,(
    ! [X29] : ~ v1_xboole_0(k1_tarski(X29)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

fof(c_0_32,plain,(
    ! [X34,X35,X36,X37] :
      ( ~ v1_funct_1(X36)
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,k1_tarski(X35))))
      | ~ v1_funct_1(X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,k1_tarski(X35))))
      | r1_partfun1(X36,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_partfun1])])])).

cnf(c_0_33,negated_conjecture,
    ( esk1_2(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),X2)) = esk8_0
    | esk1_2(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),X2)) = X1
    | k5_partfun1(esk5_0,k1_tarski(esk6_0),X2) = k1_tarski(X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(X4,X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != X4
    | ~ v1_partfun1(X1,X2)
    | ~ r1_partfun1(X5,X1)
    | X6 != k5_partfun1(X2,X3,X5)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( esk1_2(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),esk8_0)) = esk8_0
    | esk1_2(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),esk8_0)) = X1
    | k5_partfun1(esk5_0,k1_tarski(esk6_0),esk8_0) = k1_tarski(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_20]),c_0_19])])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | X2 != k5_partfun1(X3,X4,X5)
    | ~ r1_partfun1(X5,X1)
    | ~ v1_partfun1(X1,X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( v1_partfun1(esk8_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_18]),c_0_19]),c_0_20])]),c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r1_partfun1(X1,esk8_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_20]),c_0_19])])).

cnf(c_0_42,plain,
    ( v1_partfun1(esk2_5(X1,X2,X3,X4,X5),X1)
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( esk2_5(X1,X2,X3,X4,X5) = X5
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_45,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( esk1_2(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),esk8_0)) = X1
    | k5_partfun1(esk5_0,k1_tarski(esk6_0),esk8_0) = k1_tarski(X1)
    | esk8_0 != X1 ),
    inference(ef,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk8_0,X1)
    | X1 != k5_partfun1(esk5_0,k1_tarski(esk6_0),X2)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_20]),c_0_40]),c_0_19])]),c_0_41])).

cnf(c_0_48,plain,
    ( v1_partfun1(X1,X2)
    | X3 != k5_partfun1(X2,X4,X5)
    | ~ r2_hidden(X1,X3)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_tarski(X1) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( k5_partfun1(esk5_0,k1_tarski(esk6_0),esk8_0) = k1_tarski(X1)
    | esk8_0 != X1
    | ~ r2_hidden(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk8_0,k5_partfun1(esk5_0,k1_tarski(esk6_0),X1))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_52,plain,
    ( v1_partfun1(X1,X2)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_53,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k5_partfun1(X2,X3,X4) != k1_tarski(X1)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k5_partfun1(esk5_0,k1_tarski(esk6_0),esk8_0) = k1_tarski(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_19]),c_0_20])])).

cnf(c_0_55,plain,
    ( v1_funct_1(X1)
    | k5_partfun1(X2,X3,X4) != k1_tarski(X1)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_58,plain,
    ( v1_partfun1(X1,X2)
    | k5_partfun1(X2,X3,X4) != k1_tarski(X1)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0))))
    | k1_tarski(esk8_0) != k1_tarski(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_19]),c_0_20])])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_1(X1)
    | k1_tarski(esk8_0) != k1_tarski(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_54]),c_0_19]),c_0_20])])).

cnf(c_0_61,negated_conjecture,
    ( esk1_2(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0)) = esk8_0
    | esk1_2(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0)) = X1
    | k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0) = k1_tarski(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_56]),c_0_57])])).

cnf(c_0_62,negated_conjecture,
    ( v1_partfun1(X1,esk5_0)
    | k1_tarski(esk8_0) != k1_tarski(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_54]),c_0_19]),c_0_20])])).

cnf(c_0_63,negated_conjecture,
    ( r1_partfun1(X1,X2)
    | k1_tarski(esk8_0) != k1_tarski(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_59]),c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( esk1_2(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0)) = esk8_0
    | k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0) = k1_tarski(X1)
    | X1 != esk8_0 ),
    inference(ef,[status(thm)],[c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k5_partfun1(esk5_0,k1_tarski(esk6_0),X3)
    | k1_tarski(esk8_0) != k1_tarski(X1)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_59]),c_0_60]),c_0_62]),c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0) = k1_tarski(X1)
    | esk8_0 != X1
    | ~ r2_hidden(esk8_0,k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk5_0,k1_tarski(esk6_0),X2))
    | k1_tarski(esk8_0) != k1_tarski(X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_tarski(esk6_0)))) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0) = k1_tarski(X1)
    | esk8_0 != X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_57]),c_0_56])])).

cnf(c_0_69,negated_conjecture,
    ( k5_partfun1(esk5_0,k1_tarski(esk6_0),esk7_0) != k1_tarski(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_68]),c_0_69]),
    [proof]).

%------------------------------------------------------------------------------
