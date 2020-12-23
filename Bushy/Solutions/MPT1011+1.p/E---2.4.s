%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t66_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:48 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   24 (  99 expanded)
%              Number of clauses        :   17 (  31 expanded)
%              Number of leaves         :    3 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :  109 ( 561 expanded)
%              Number of equality atoms :    9 (  14 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t66_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,k1_tarski(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,k1_tarski(X2))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => r2_relset_1(X1,k1_tarski(X2),X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t66_funct_2.p',t66_funct_2)).

fof(t65_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,k1_tarski(X2))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ( r2_hidden(X3,X1)
       => k1_funct_1(X4,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t66_funct_2.p',t65_funct_2)).

fof(t18_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ! [X5] :
                ( r2_hidden(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
           => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t66_funct_2.p',t18_funct_2)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,k1_tarski(X2))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,k1_tarski(X2))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
           => r2_relset_1(X1,k1_tarski(X2),X3,X4) ) ) ),
    inference(assume_negation,[status(cth)],[t66_funct_2])).

fof(c_0_4,plain,(
    ! [X43,X44,X45,X46] :
      ( ~ v1_funct_1(X46)
      | ~ v1_funct_2(X46,X43,k1_tarski(X44))
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,k1_tarski(X44))))
      | ~ r2_hidden(X45,X43)
      | k1_funct_1(X46,X45) = X44 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_2])])).

fof(c_0_5,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,k1_tarski(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_tarski(esk2_0))))
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,k1_tarski(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_tarski(esk2_0))))
    & ~ r2_relset_1(esk1_0,k1_tarski(esk2_0),esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X26,X27,X28,X29] :
      ( ( r2_hidden(esk6_4(X26,X27,X28,X29),X26)
        | r2_relset_1(X26,X27,X28,X29)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,X26,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( k1_funct_1(X28,esk6_4(X26,X27,X28,X29)) != k1_funct_1(X29,esk6_4(X26,X27,X28,X29))
        | r2_relset_1(X26,X27,X28,X29)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,X26,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_funct_2])])])])])).

cnf(c_0_7,plain,
    ( k1_funct_1(X1,X4) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,k1_tarski(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_tarski(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,k1_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( r2_relset_1(X2,X3,X1,X4)
    | k1_funct_1(X1,esk6_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk6_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = esk2_0
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10])])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_tarski(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,k1_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),X1)
    | r2_relset_1(X1,X2,X3,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( r2_relset_1(X1,X2,X3,esk4_0)
    | k1_funct_1(X3,esk6_4(X1,X2,X3,esk4_0)) != esk2_0
    | ~ r2_hidden(esk6_4(X1,X2,X3,esk4_0),esk1_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(esk4_0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_10])])).

cnf(c_0_18,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = esk2_0
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk6_4(esk1_0,k1_tarski(esk2_0),X1,esk4_0),esk1_0)
    | r2_relset_1(esk1_0,k1_tarski(esk2_0),X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_tarski(esk2_0))))
    | ~ v1_funct_2(X1,esk1_0,k1_tarski(esk2_0))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_8]),c_0_9]),c_0_10])])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,k1_tarski(esk2_0),esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( r2_relset_1(X1,X2,esk3_0,esk4_0)
    | ~ r2_hidden(esk6_4(X1,X2,esk3_0,esk4_0),esk1_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(esk4_0,X1,X2)
    | ~ v1_funct_2(esk3_0,X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_15])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk6_4(esk1_0,k1_tarski(esk2_0),esk3_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_13]),c_0_14]),c_0_15])]),c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_8]),c_0_13]),c_0_9]),c_0_14])]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
