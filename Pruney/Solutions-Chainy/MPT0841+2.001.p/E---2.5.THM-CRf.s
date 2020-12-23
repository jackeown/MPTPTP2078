%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:42 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 361 expanded)
%              Number of clauses        :   37 ( 154 expanded)
%              Number of leaves         :   10 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  200 (1915 expanded)
%              Number of equality atoms :    7 (  45 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
                      <=> ? [X6] :
                            ( m1_subset_1(X6,X3)
                            & r2_hidden(k4_tarski(X6,X5),X4)
                            & r2_hidden(X6,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t74_relat_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ~ v1_xboole_0(X3)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
                        <=> ? [X6] :
                              ( m1_subset_1(X6,X3)
                              & r2_hidden(k4_tarski(X6,X5),X4)
                              & r2_hidden(X6,X2) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relset_1])).

fof(c_0_11,plain,(
    ! [X31,X32,X33,X34] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k7_relset_1(X31,X32,X33,X34) = k9_relat_1(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_12,negated_conjecture,(
    ! [X40] :
      ( ~ v1_xboole_0(esk2_0)
      & ~ v1_xboole_0(esk3_0)
      & ~ v1_xboole_0(esk4_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))
      & m1_subset_1(esk6_0,esk2_0)
      & ( ~ r2_hidden(esk6_0,k7_relset_1(esk4_0,esk2_0,esk5_0,esk3_0))
        | ~ m1_subset_1(X40,esk4_0)
        | ~ r2_hidden(k4_tarski(X40,esk6_0),esk5_0)
        | ~ r2_hidden(X40,esk3_0) )
      & ( m1_subset_1(esk7_0,esk4_0)
        | r2_hidden(esk6_0,k7_relset_1(esk4_0,esk2_0,esk5_0,esk3_0)) )
      & ( r2_hidden(k4_tarski(esk7_0,esk6_0),esk5_0)
        | r2_hidden(esk6_0,k7_relset_1(esk4_0,esk2_0,esk5_0,esk3_0)) )
      & ( r2_hidden(esk7_0,esk3_0)
        | r2_hidden(esk6_0,k7_relset_1(esk4_0,esk2_0,esk5_0,esk3_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).

cnf(c_0_13,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | v1_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_16,plain,(
    ! [X19,X20,X21,X22] :
      ( ( r2_hidden(X19,X21)
        | ~ r2_hidden(k4_tarski(X19,X20),k5_relat_1(k6_relat_1(X21),X22))
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(k4_tarski(X19,X20),X22)
        | ~ r2_hidden(k4_tarski(X19,X20),k5_relat_1(k6_relat_1(X21),X22))
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(X19,X21)
        | ~ r2_hidden(k4_tarski(X19,X20),X22)
        | r2_hidden(k4_tarski(X19,X20),k5_relat_1(k6_relat_1(X21),X22))
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_relat_1])])])).

fof(c_0_17,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | ~ r1_tarski(k1_relat_1(X24),X23)
      | k5_relat_1(k6_relat_1(X23),X24) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k7_relset_1(esk4_0,esk2_0,esk5_0,esk3_0))
    | ~ m1_subset_1(X1,esk4_0)
    | ~ r2_hidden(k4_tarski(X1,esk6_0),esk5_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( k7_relset_1(esk4_0,esk2_0,esk5_0,X1) = k9_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_20,plain,(
    ! [X11,X12,X13,X15] :
      ( ( r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X13))
        | ~ r2_hidden(X11,k9_relat_1(X13,X12))
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk1_3(X11,X12,X13),X11),X13)
        | ~ r2_hidden(X11,k9_relat_1(X13,X12))
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X12)
        | ~ r2_hidden(X11,k9_relat_1(X13,X12))
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(X15,k1_relat_1(X13))
        | ~ r2_hidden(k4_tarski(X15,X11),X13)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X11,k9_relat_1(X13,X12))
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_21,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k5_relat_1(k6_relat_1(X2),X4))
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( ~ m1_subset_1(X1,esk4_0)
    | ~ r2_hidden(esk6_0,k9_relat_1(esk5_0,esk3_0))
    | ~ r2_hidden(k4_tarski(X1,esk6_0),esk5_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_14])).

fof(c_0_27,plain,(
    ! [X7,X8] :
      ( ~ r2_hidden(X7,X8)
      | m1_subset_1(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_relat_1(X3),X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X4),X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( ~ m1_subset_1(esk1_3(esk6_0,X1,esk5_0),esk4_0)
    | ~ r2_hidden(esk1_3(esk6_0,X1,esk5_0),esk3_0)
    | ~ r2_hidden(esk6_0,k9_relat_1(esk5_0,esk3_0))
    | ~ r2_hidden(esk6_0,k9_relat_1(esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk7_0,esk3_0)
    | r2_hidden(esk6_0,k7_relset_1(esk4_0,esk2_0,esk5_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X4)
    | ~ r1_tarski(k1_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_25])).

fof(c_0_34,plain,(
    ! [X16,X17,X18] :
      ( ( r2_hidden(X16,k1_relat_1(X18))
        | ~ r2_hidden(k4_tarski(X16,X17),X18)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(X17,k2_relat_1(X18))
        | ~ r2_hidden(k4_tarski(X16,X17),X18)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_35,negated_conjecture,
    ( ~ m1_subset_1(esk1_3(esk6_0,esk3_0,esk5_0),esk4_0)
    | ~ r2_hidden(esk6_0,k9_relat_1(esk5_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_26])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk6_0,k9_relat_1(esk5_0,esk3_0))
    | r2_hidden(esk7_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_19])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X4)
    | ~ r1_tarski(k1_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_38,plain,(
    ! [X28,X29,X30] :
      ( ( v4_relat_1(X30,X28)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( v5_relat_1(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_39,plain,
    ( r2_hidden(X3,k9_relat_1(X2,X4))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk6_0),esk5_0)
    | r2_hidden(esk6_0,k7_relset_1(esk4_0,esk2_0,esk5_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk7_0,esk3_0)
    | ~ m1_subset_1(esk1_3(esk6_0,esk3_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk1_3(esk6_0,esk3_0,esk5_0),X1)
    | r2_hidden(esk7_0,esk3_0)
    | ~ r1_tarski(k1_relat_1(esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_36]),c_0_26])])).

fof(c_0_44,plain,(
    ! [X9,X10] :
      ( ( ~ v4_relat_1(X10,X9)
        | r1_tarski(k1_relat_1(X10),X9)
        | ~ v1_relat_1(X10) )
      & ( ~ r1_tarski(k1_relat_1(X10),X9)
        | v4_relat_1(X10,X9)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_45,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk6_0),esk5_0)
    | r2_hidden(esk6_0,k9_relat_1(esk5_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk7_0,esk3_0)
    | ~ r1_tarski(k1_relat_1(esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( v4_relat_1(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_14])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk6_0,k9_relat_1(esk5_0,esk3_0))
    | r2_hidden(esk6_0,k9_relat_1(esk5_0,X1))
    | ~ r2_hidden(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_26])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk7_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_26])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk6_0,k9_relat_1(esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( ~ m1_subset_1(esk1_3(esk6_0,esk3_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_53])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk1_3(esk6_0,esk3_0,esk5_0),X1)
    | ~ r1_tarski(k1_relat_1(esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_53]),c_0_26])])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_49]),c_0_50]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:15:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.42  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.21/0.42  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.42  #
% 0.21/0.42  # Preprocessing time       : 0.027 s
% 0.21/0.42  
% 0.21/0.42  # Proof found!
% 0.21/0.42  # SZS status Theorem
% 0.21/0.42  # SZS output start CNFRefutation
% 0.21/0.42  fof(t52_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 0.21/0.42  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.21/0.42  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.21/0.42  fof(t74_relat_1, axiom, ![X1, X2, X3, X4]:(v1_relat_1(X4)=>(r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))<=>(r2_hidden(X1,X3)&r2_hidden(k4_tarski(X1,X2),X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_relat_1)).
% 0.21/0.42  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 0.21/0.42  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.21/0.42  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.21/0.42  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 0.21/0.42  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.21/0.42  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.21/0.42  fof(c_0_10, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2))))))))), inference(assume_negation,[status(cth)],[t52_relset_1])).
% 0.21/0.42  fof(c_0_11, plain, ![X31, X32, X33, X34]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k7_relset_1(X31,X32,X33,X34)=k9_relat_1(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.21/0.42  fof(c_0_12, negated_conjecture, ![X40]:(~v1_xboole_0(esk2_0)&(~v1_xboole_0(esk3_0)&(~v1_xboole_0(esk4_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))&(m1_subset_1(esk6_0,esk2_0)&((~r2_hidden(esk6_0,k7_relset_1(esk4_0,esk2_0,esk5_0,esk3_0))|(~m1_subset_1(X40,esk4_0)|~r2_hidden(k4_tarski(X40,esk6_0),esk5_0)|~r2_hidden(X40,esk3_0)))&(((m1_subset_1(esk7_0,esk4_0)|r2_hidden(esk6_0,k7_relset_1(esk4_0,esk2_0,esk5_0,esk3_0)))&(r2_hidden(k4_tarski(esk7_0,esk6_0),esk5_0)|r2_hidden(esk6_0,k7_relset_1(esk4_0,esk2_0,esk5_0,esk3_0))))&(r2_hidden(esk7_0,esk3_0)|r2_hidden(esk6_0,k7_relset_1(esk4_0,esk2_0,esk5_0,esk3_0)))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).
% 0.21/0.42  cnf(c_0_13, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.42  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.42  fof(c_0_15, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|v1_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.21/0.42  fof(c_0_16, plain, ![X19, X20, X21, X22]:(((r2_hidden(X19,X21)|~r2_hidden(k4_tarski(X19,X20),k5_relat_1(k6_relat_1(X21),X22))|~v1_relat_1(X22))&(r2_hidden(k4_tarski(X19,X20),X22)|~r2_hidden(k4_tarski(X19,X20),k5_relat_1(k6_relat_1(X21),X22))|~v1_relat_1(X22)))&(~r2_hidden(X19,X21)|~r2_hidden(k4_tarski(X19,X20),X22)|r2_hidden(k4_tarski(X19,X20),k5_relat_1(k6_relat_1(X21),X22))|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_relat_1])])])).
% 0.21/0.42  fof(c_0_17, plain, ![X23, X24]:(~v1_relat_1(X24)|(~r1_tarski(k1_relat_1(X24),X23)|k5_relat_1(k6_relat_1(X23),X24)=X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.21/0.42  cnf(c_0_18, negated_conjecture, (~r2_hidden(esk6_0,k7_relset_1(esk4_0,esk2_0,esk5_0,esk3_0))|~m1_subset_1(X1,esk4_0)|~r2_hidden(k4_tarski(X1,esk6_0),esk5_0)|~r2_hidden(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.42  cnf(c_0_19, negated_conjecture, (k7_relset_1(esk4_0,esk2_0,esk5_0,X1)=k9_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.42  fof(c_0_20, plain, ![X11, X12, X13, X15]:((((r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X13))|~r2_hidden(X11,k9_relat_1(X13,X12))|~v1_relat_1(X13))&(r2_hidden(k4_tarski(esk1_3(X11,X12,X13),X11),X13)|~r2_hidden(X11,k9_relat_1(X13,X12))|~v1_relat_1(X13)))&(r2_hidden(esk1_3(X11,X12,X13),X12)|~r2_hidden(X11,k9_relat_1(X13,X12))|~v1_relat_1(X13)))&(~r2_hidden(X15,k1_relat_1(X13))|~r2_hidden(k4_tarski(X15,X11),X13)|~r2_hidden(X15,X12)|r2_hidden(X11,k9_relat_1(X13,X12))|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.21/0.42  cnf(c_0_21, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.42  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k5_relat_1(k6_relat_1(X2),X4))|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.42  cnf(c_0_23, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.42  cnf(c_0_24, negated_conjecture, (~m1_subset_1(X1,esk4_0)|~r2_hidden(esk6_0,k9_relat_1(esk5_0,esk3_0))|~r2_hidden(k4_tarski(X1,esk6_0),esk5_0)|~r2_hidden(X1,esk3_0)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.21/0.42  cnf(c_0_25, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.42  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_14])).
% 0.21/0.42  fof(c_0_27, plain, ![X7, X8]:(~r2_hidden(X7,X8)|m1_subset_1(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.21/0.42  cnf(c_0_28, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_relat_1(X3),X2)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X4),X3)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.21/0.42  cnf(c_0_29, negated_conjecture, (~m1_subset_1(esk1_3(esk6_0,X1,esk5_0),esk4_0)|~r2_hidden(esk1_3(esk6_0,X1,esk5_0),esk3_0)|~r2_hidden(esk6_0,k9_relat_1(esk5_0,esk3_0))|~r2_hidden(esk6_0,k9_relat_1(esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.21/0.42  cnf(c_0_30, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.42  cnf(c_0_31, negated_conjecture, (r2_hidden(esk7_0,esk3_0)|r2_hidden(esk6_0,k7_relset_1(esk4_0,esk2_0,esk5_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.42  cnf(c_0_32, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.42  cnf(c_0_33, plain, (r2_hidden(esk1_3(X1,X2,X3),X4)|~r1_tarski(k1_relat_1(X3),X4)|~v1_relat_1(X3)|~r2_hidden(X1,k9_relat_1(X3,X2))), inference(spm,[status(thm)],[c_0_28, c_0_25])).
% 0.21/0.42  fof(c_0_34, plain, ![X16, X17, X18]:((r2_hidden(X16,k1_relat_1(X18))|~r2_hidden(k4_tarski(X16,X17),X18)|~v1_relat_1(X18))&(r2_hidden(X17,k2_relat_1(X18))|~r2_hidden(k4_tarski(X16,X17),X18)|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.21/0.42  cnf(c_0_35, negated_conjecture, (~m1_subset_1(esk1_3(esk6_0,esk3_0,esk5_0),esk4_0)|~r2_hidden(esk6_0,k9_relat_1(esk5_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_26])])).
% 0.21/0.42  cnf(c_0_36, negated_conjecture, (r2_hidden(esk6_0,k9_relat_1(esk5_0,esk3_0))|r2_hidden(esk7_0,esk3_0)), inference(rw,[status(thm)],[c_0_31, c_0_19])).
% 0.21/0.42  cnf(c_0_37, plain, (m1_subset_1(esk1_3(X1,X2,X3),X4)|~r1_tarski(k1_relat_1(X3),X4)|~v1_relat_1(X3)|~r2_hidden(X1,k9_relat_1(X3,X2))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.42  fof(c_0_38, plain, ![X28, X29, X30]:((v4_relat_1(X30,X28)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))&(v5_relat_1(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.21/0.42  cnf(c_0_39, plain, (r2_hidden(X3,k9_relat_1(X2,X4))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.42  cnf(c_0_40, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.42  cnf(c_0_41, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk6_0),esk5_0)|r2_hidden(esk6_0,k7_relset_1(esk4_0,esk2_0,esk5_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.42  cnf(c_0_42, negated_conjecture, (r2_hidden(esk7_0,esk3_0)|~m1_subset_1(esk1_3(esk6_0,esk3_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.42  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk1_3(esk6_0,esk3_0,esk5_0),X1)|r2_hidden(esk7_0,esk3_0)|~r1_tarski(k1_relat_1(esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_36]), c_0_26])])).
% 0.21/0.42  fof(c_0_44, plain, ![X9, X10]:((~v4_relat_1(X10,X9)|r1_tarski(k1_relat_1(X10),X9)|~v1_relat_1(X10))&(~r1_tarski(k1_relat_1(X10),X9)|v4_relat_1(X10,X9)|~v1_relat_1(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.21/0.42  cnf(c_0_45, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.42  cnf(c_0_46, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X1),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.42  cnf(c_0_47, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk6_0),esk5_0)|r2_hidden(esk6_0,k9_relat_1(esk5_0,esk3_0))), inference(rw,[status(thm)],[c_0_41, c_0_19])).
% 0.21/0.42  cnf(c_0_48, negated_conjecture, (r2_hidden(esk7_0,esk3_0)|~r1_tarski(k1_relat_1(esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.42  cnf(c_0_49, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.42  cnf(c_0_50, negated_conjecture, (v4_relat_1(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_45, c_0_14])).
% 0.21/0.42  cnf(c_0_51, negated_conjecture, (r2_hidden(esk6_0,k9_relat_1(esk5_0,esk3_0))|r2_hidden(esk6_0,k9_relat_1(esk5_0,X1))|~r2_hidden(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_26])])).
% 0.21/0.42  cnf(c_0_52, negated_conjecture, (r2_hidden(esk7_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_26])])).
% 0.21/0.42  cnf(c_0_53, negated_conjecture, (r2_hidden(esk6_0,k9_relat_1(esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.42  cnf(c_0_54, negated_conjecture, (~m1_subset_1(esk1_3(esk6_0,esk3_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_53])])).
% 0.21/0.42  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk1_3(esk6_0,esk3_0,esk5_0),X1)|~r1_tarski(k1_relat_1(esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_53]), c_0_26])])).
% 0.21/0.42  cnf(c_0_56, negated_conjecture, (~r1_tarski(k1_relat_1(esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.42  cnf(c_0_57, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_49]), c_0_50]), c_0_26])]), ['proof']).
% 0.21/0.42  # SZS output end CNFRefutation
% 0.21/0.42  # Proof object total steps             : 58
% 0.21/0.42  # Proof object clause steps            : 37
% 0.21/0.42  # Proof object formula steps           : 21
% 0.21/0.42  # Proof object conjectures             : 25
% 0.21/0.42  # Proof object clause conjectures      : 22
% 0.21/0.42  # Proof object formula conjectures     : 3
% 0.21/0.42  # Proof object initial clauses used    : 15
% 0.21/0.42  # Proof object initial formulas used   : 10
% 0.21/0.42  # Proof object generating inferences   : 17
% 0.21/0.42  # Proof object simplifying inferences  : 22
% 0.21/0.42  # Training examples: 0 positive, 0 negative
% 0.21/0.42  # Parsed axioms                        : 10
% 0.21/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.42  # Initial clauses                      : 26
% 0.21/0.42  # Removed in clause preprocessing      : 0
% 0.21/0.42  # Initial clauses in saturation        : 26
% 0.21/0.42  # Processed clauses                    : 613
% 0.21/0.42  # ...of these trivial                  : 1
% 0.21/0.42  # ...subsumed                          : 297
% 0.21/0.42  # ...remaining for further processing  : 315
% 0.21/0.42  # Other redundant clauses eliminated   : 0
% 0.21/0.42  # Clauses deleted for lack of memory   : 0
% 0.21/0.42  # Backward-subsumed                    : 61
% 0.21/0.42  # Backward-rewritten                   : 121
% 0.21/0.42  # Generated clauses                    : 1014
% 0.21/0.42  # ...of the previous two non-trivial   : 990
% 0.21/0.42  # Contextual simplify-reflections      : 6
% 0.21/0.42  # Paramodulations                      : 1014
% 0.21/0.42  # Factorizations                       : 0
% 0.21/0.42  # Equation resolutions                 : 0
% 0.21/0.42  # Propositional unsat checks           : 0
% 0.21/0.42  #    Propositional check models        : 0
% 0.21/0.42  #    Propositional check unsatisfiable : 0
% 0.21/0.42  #    Propositional clauses             : 0
% 0.21/0.42  #    Propositional clauses after purity: 0
% 0.21/0.42  #    Propositional unsat core size     : 0
% 0.21/0.42  #    Propositional preprocessing time  : 0.000
% 0.21/0.42  #    Propositional encoding time       : 0.000
% 0.21/0.42  #    Propositional solver time         : 0.000
% 0.21/0.42  #    Success case prop preproc time    : 0.000
% 0.21/0.42  #    Success case prop encoding time   : 0.000
% 0.21/0.42  #    Success case prop solver time     : 0.000
% 0.21/0.42  # Current number of processed clauses  : 133
% 0.21/0.42  #    Positive orientable unit clauses  : 17
% 0.21/0.42  #    Positive unorientable unit clauses: 0
% 0.21/0.42  #    Negative unit clauses             : 5
% 0.21/0.42  #    Non-unit-clauses                  : 111
% 0.21/0.42  # Current number of unprocessed clauses: 362
% 0.21/0.42  # ...number of literals in the above   : 1897
% 0.21/0.42  # Current number of archived formulas  : 0
% 0.21/0.42  # Current number of archived clauses   : 182
% 0.21/0.42  # Clause-clause subsumption calls (NU) : 9354
% 0.21/0.42  # Rec. Clause-clause subsumption calls : 3351
% 0.21/0.42  # Non-unit clause-clause subsumptions  : 334
% 0.21/0.42  # Unit Clause-clause subsumption calls : 345
% 0.21/0.42  # Rewrite failures with RHS unbound    : 0
% 0.21/0.42  # BW rewrite match attempts            : 11
% 0.21/0.42  # BW rewrite match successes           : 11
% 0.21/0.42  # Condensation attempts                : 0
% 0.21/0.42  # Condensation successes               : 0
% 0.21/0.42  # Termbank termtop insertions          : 27640
% 0.21/0.42  
% 0.21/0.42  # -------------------------------------------------
% 0.21/0.42  # User time                : 0.075 s
% 0.21/0.42  # System time              : 0.007 s
% 0.21/0.42  # Total time               : 0.083 s
% 0.21/0.42  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
