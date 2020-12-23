%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t165_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:35 EDT 2019

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 213 expanded)
%              Number of clauses        :   33 (  82 expanded)
%              Number of leaves         :    8 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  257 (1003 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t165_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r1_relset_1(X1,X2,X4,X3)
           => r1_tarski(k5_partfun1(X1,X2,X3),k5_partfun1(X1,X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t165_funct_2.p',t165_funct_2)).

fof(t168_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
         => ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t165_funct_2.p',t168_partfun1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t165_funct_2.p',d3_tarski)).

fof(t171_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_relat_1(X4)
            & v1_funct_1(X4) )
         => ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
           => r1_partfun1(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t165_funct_2.p',t171_partfun1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t165_funct_2.p',cc1_relset_1)).

fof(t169_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
           => v1_partfun1(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t165_funct_2.p',t169_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/funct_2__t165_funct_2.p',d7_partfun1)).

fof(t140_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ! [X5] :
              ( ( v1_relat_1(X5)
                & v1_funct_1(X5) )
             => ( ( r1_partfun1(X3,X5)
                  & r1_relset_1(X1,X2,X4,X3) )
               => r1_partfun1(X4,X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t165_funct_2.p',t140_partfun1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( r1_relset_1(X1,X2,X4,X3)
             => r1_tarski(k5_partfun1(X1,X2,X3),k5_partfun1(X1,X2,X4)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t165_funct_2])).

fof(c_0_9,plain,(
    ! [X49,X50,X51,X52] :
      ( ( v1_funct_1(X52)
        | ~ r2_hidden(X52,k5_partfun1(X49,X50,X51))
        | ~ v1_funct_1(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
        | ~ r2_hidden(X52,k5_partfun1(X49,X50,X51))
        | ~ v1_funct_1(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_partfun1])])])])).

fof(c_0_10,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v1_funct_1(esk4_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r1_relset_1(esk1_0,esk2_0,esk4_0,esk3_0)
    & ~ r1_tarski(k5_partfun1(esk1_0,esk2_0,esk3_0),k5_partfun1(esk1_0,esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( ~ r1_tarski(X13,X14)
        | ~ r2_hidden(X15,X13)
        | r2_hidden(X15,X14) )
      & ( r2_hidden(esk5_2(X16,X17),X16)
        | r1_tarski(X16,X17) )
      & ( ~ r2_hidden(esk5_2(X16,X17),X17)
        | r1_tarski(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X57,X58,X59,X60] :
      ( ~ v1_funct_1(X59)
      | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
      | ~ v1_relat_1(X60)
      | ~ v1_funct_1(X60)
      | ~ r2_hidden(X60,k5_partfun1(X57,X58,X59))
      | r1_partfun1(X59,X60) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_partfun1])])])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(esk1_0,esk2_0,esk3_0),k5_partfun1(esk1_0,esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4)
    | ~ r2_hidden(X4,k5_partfun1(X2,X3,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_20,plain,(
    ! [X78,X79,X80] :
      ( ~ m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X78,X79)))
      | v1_relat_1(X80) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ r2_hidden(X1,k5_partfun1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk5_2(k5_partfun1(esk1_0,esk2_0,esk3_0),k5_partfun1(esk1_0,esk2_0,esk4_0)),k5_partfun1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_23,plain,(
    ! [X53,X54,X55,X56] :
      ( ~ v1_funct_1(X55)
      | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
      | ~ v1_funct_1(X56)
      | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
      | ~ r2_hidden(X56,k5_partfun1(X53,X54,X55))
      | v1_partfun1(X56,X53) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_partfun1])])])).

fof(c_0_24,plain,(
    ! [X19,X20,X21,X22,X23,X25,X26,X27,X29] :
      ( ( v1_funct_1(esk6_5(X19,X20,X21,X22,X23))
        | ~ r2_hidden(X23,X22)
        | X22 != k5_partfun1(X19,X20,X21)
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( m1_subset_1(esk6_5(X19,X20,X21,X22,X23),k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ r2_hidden(X23,X22)
        | X22 != k5_partfun1(X19,X20,X21)
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( esk6_5(X19,X20,X21,X22,X23) = X23
        | ~ r2_hidden(X23,X22)
        | X22 != k5_partfun1(X19,X20,X21)
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( v1_partfun1(esk6_5(X19,X20,X21,X22,X23),X19)
        | ~ r2_hidden(X23,X22)
        | X22 != k5_partfun1(X19,X20,X21)
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( r1_partfun1(X21,esk6_5(X19,X20,X21,X22,X23))
        | ~ r2_hidden(X23,X22)
        | X22 != k5_partfun1(X19,X20,X21)
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( ~ v1_funct_1(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | X26 != X25
        | ~ v1_partfun1(X26,X19)
        | ~ r1_partfun1(X21,X26)
        | r2_hidden(X25,X22)
        | X22 != k5_partfun1(X19,X20,X21)
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( ~ r2_hidden(esk7_4(X19,X20,X21,X27),X27)
        | ~ v1_funct_1(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | X29 != esk7_4(X19,X20,X21,X27)
        | ~ v1_partfun1(X29,X19)
        | ~ r1_partfun1(X21,X29)
        | X27 = k5_partfun1(X19,X20,X21)
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( v1_funct_1(esk8_4(X19,X20,X21,X27))
        | r2_hidden(esk7_4(X19,X20,X21,X27),X27)
        | X27 = k5_partfun1(X19,X20,X21)
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( m1_subset_1(esk8_4(X19,X20,X21,X27),k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | r2_hidden(esk7_4(X19,X20,X21,X27),X27)
        | X27 = k5_partfun1(X19,X20,X21)
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( esk8_4(X19,X20,X21,X27) = esk7_4(X19,X20,X21,X27)
        | r2_hidden(esk7_4(X19,X20,X21,X27),X27)
        | X27 = k5_partfun1(X19,X20,X21)
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( v1_partfun1(esk8_4(X19,X20,X21,X27),X19)
        | r2_hidden(esk7_4(X19,X20,X21,X27),X27)
        | X27 = k5_partfun1(X19,X20,X21)
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( r1_partfun1(X21,esk8_4(X19,X20,X21,X27))
        | r2_hidden(esk7_4(X19,X20,X21,X27),X27)
        | X27 = k5_partfun1(X19,X20,X21)
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

fof(c_0_25,plain,(
    ! [X44,X45,X46,X47,X48] :
      ( ~ v1_funct_1(X46)
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | ~ v1_funct_1(X47)
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | ~ v1_relat_1(X48)
      | ~ v1_funct_1(X48)
      | ~ r1_partfun1(X46,X48)
      | ~ r1_relset_1(X44,X45,X47,X46)
      | r1_partfun1(X47,X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_partfun1])])])).

cnf(c_0_26,plain,
    ( r1_partfun1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X2,k5_partfun1(X3,X4,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk5_2(k5_partfun1(esk1_0,esk2_0,esk3_0),k5_partfun1(esk1_0,esk2_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( v1_partfun1(X4,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,k5_partfun1(X2,X3,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(X4,X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != X4
    | ~ v1_partfun1(X1,X2)
    | ~ r1_partfun1(X5,X1)
    | X6 != k5_partfun1(X2,X3,X5)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_partfun1(X4,X5)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X5)
    | ~ v1_funct_1(X5)
    | ~ r1_partfun1(X1,X5)
    | ~ r1_relset_1(X2,X3,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r1_relset_1(esk1_0,esk2_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( r1_partfun1(esk3_0,X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_14]),c_0_15])])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk5_2(k5_partfun1(esk1_0,esk2_0,esk3_0),k5_partfun1(esk1_0,esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_14]),c_0_15])])).

cnf(c_0_38,plain,
    ( v1_partfun1(X1,X2)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_29,c_0_19]),c_0_13])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ r1_partfun1(X4,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).

cnf(c_0_40,negated_conjecture,
    ( r1_partfun1(esk4_0,X1)
    | ~ v1_relat_1(X1)
    | ~ r1_partfun1(esk3_0,X1)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_14]),c_0_34]),c_0_15])])).

cnf(c_0_41,negated_conjecture,
    ( r1_partfun1(esk3_0,esk5_2(k5_partfun1(esk1_0,esk2_0,esk3_0),k5_partfun1(esk1_0,esk2_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_22]),c_0_36])])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk5_2(k5_partfun1(esk1_0,esk2_0,esk3_0),k5_partfun1(esk1_0,esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( v1_partfun1(X1,esk1_0)
    | ~ r2_hidden(X1,k5_partfun1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_14]),c_0_15])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk1_0,esk2_0,esk4_0))
    | ~ r1_partfun1(esk4_0,X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_33]),c_0_34])])).

cnf(c_0_45,negated_conjecture,
    ( r1_partfun1(esk4_0,esk5_2(k5_partfun1(esk1_0,esk2_0,esk3_0),k5_partfun1(esk1_0,esk2_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_36]),c_0_42])])).

cnf(c_0_46,negated_conjecture,
    ( v1_partfun1(esk5_2(k5_partfun1(esk1_0,esk2_0,esk3_0),k5_partfun1(esk1_0,esk2_0,esk4_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_22])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk5_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk5_2(k5_partfun1(esk1_0,esk2_0,esk3_0),k5_partfun1(esk1_0,esk2_0,esk4_0)),k5_partfun1(esk1_0,esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_28]),c_0_42])]),c_0_45]),c_0_46])])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
