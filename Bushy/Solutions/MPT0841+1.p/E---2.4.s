%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relset_1__t52_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:11 EDT 2019

% Result     : Theorem 268.91s
% Output     : CNFRefutation 268.91s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 628 expanded)
%              Number of clauses        :   59 ( 284 expanded)
%              Number of leaves         :   10 ( 143 expanded)
%              Depth                    :   19
%              Number of atoms          :  247 (3190 expanded)
%              Number of equality atoms :   14 ( 140 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t52_relset_1.p',t7_boole)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t52_relset_1.p',t106_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/relset_1__t52_relset_1.p',t52_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t52_relset_1.p',t2_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t52_relset_1.p',t4_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t52_relset_1.p',existence_m1_subset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t52_relset_1.p',redefinition_k7_relset_1)).

fof(d13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t52_relset_1.p',d13_relat_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t52_relset_1.p',t1_subset)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t52_relset_1.p',cc1_relset_1)).

fof(c_0_10,plain,(
    ! [X55,X56] :
      ( ~ r2_hidden(X55,X56)
      | ~ v1_xboole_0(X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_11,plain,(
    ! [X38,X39,X40,X41] :
      ( ( r2_hidden(X38,X40)
        | ~ r2_hidden(k4_tarski(X38,X39),k2_zfmisc_1(X40,X41)) )
      & ( r2_hidden(X39,X41)
        | ~ r2_hidden(k4_tarski(X38,X39),k2_zfmisc_1(X40,X41)) )
      & ( ~ r2_hidden(X38,X40)
        | ~ r2_hidden(X39,X41)
        | r2_hidden(k4_tarski(X38,X39),k2_zfmisc_1(X40,X41)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

fof(c_0_12,negated_conjecture,(
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

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X44,X45] :
      ( ~ m1_subset_1(X44,X45)
      | v1_xboole_0(X45)
      | r2_hidden(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_16,plain,(
    ! [X48,X49,X50] :
      ( ~ r2_hidden(X48,X49)
      | ~ m1_subset_1(X49,k1_zfmisc_1(X50))
      | m1_subset_1(X48,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_17,negated_conjecture,(
    ! [X12] :
      ( ~ v1_xboole_0(esk1_0)
      & ~ v1_xboole_0(esk2_0)
      & ~ v1_xboole_0(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))
      & m1_subset_1(esk5_0,esk1_0)
      & ( ~ r2_hidden(esk5_0,k7_relset_1(esk3_0,esk1_0,esk4_0,esk2_0))
        | ~ m1_subset_1(X12,esk3_0)
        | ~ r2_hidden(k4_tarski(X12,esk5_0),esk4_0)
        | ~ r2_hidden(X12,esk2_0) )
      & ( m1_subset_1(esk6_0,esk3_0)
        | r2_hidden(esk5_0,k7_relset_1(esk3_0,esk1_0,esk4_0,esk2_0)) )
      & ( r2_hidden(k4_tarski(esk6_0,esk5_0),esk4_0)
        | r2_hidden(esk5_0,k7_relset_1(esk3_0,esk1_0,esk4_0,esk2_0)) )
      & ( r2_hidden(esk6_0,esk2_0)
        | r2_hidden(esk5_0,k7_relset_1(esk3_0,esk1_0,esk4_0,esk2_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | ~ v1_xboole_0(k2_zfmisc_1(X4,X2)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X32] : m1_subset_1(esk10_1(X32),X32) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X5,X2)
    | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(esk3_0,esk1_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,esk1_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk10_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_29,plain,(
    ! [X34,X35,X36,X37] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k7_relset_1(X34,X35,X36,X37) = k9_relat_1(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk3_0,esk1_0))
    | ~ r2_hidden(X2,esk1_0)
    | ~ r2_hidden(X3,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk10_1(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_19])).

fof(c_0_33,plain,(
    ! [X16,X17,X18,X19,X21,X22,X23,X24,X26] :
      ( ( r2_hidden(k4_tarski(esk7_4(X16,X17,X18,X19),X19),X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k9_relat_1(X16,X17)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk7_4(X16,X17,X18,X19),X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k9_relat_1(X16,X17)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X22,X21),X16)
        | ~ r2_hidden(X22,X17)
        | r2_hidden(X21,X18)
        | X18 != k9_relat_1(X16,X17)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(esk8_3(X16,X23,X24),X24)
        | ~ r2_hidden(k4_tarski(X26,esk8_3(X16,X23,X24)),X16)
        | ~ r2_hidden(X26,X23)
        | X24 = k9_relat_1(X16,X23)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk9_3(X16,X23,X24),esk8_3(X16,X23,X24)),X16)
        | r2_hidden(esk8_3(X16,X23,X24),X24)
        | X24 = k9_relat_1(X16,X23)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk9_3(X16,X23,X24),X23)
        | r2_hidden(esk8_3(X16,X23,X24),X24)
        | X24 = k9_relat_1(X16,X23)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

cnf(c_0_34,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk3_0,esk1_0))
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk10_1(esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_27])).

cnf(c_0_37,plain,
    ( r2_hidden(esk7_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk5_0),esk4_0)
    | r2_hidden(esk5_0,k7_relset_1(esk3_0,esk1_0,esk4_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( k7_relset_1(esk3_0,esk1_0,esk4_0,X1) = k9_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k7_relset_1(esk3_0,esk1_0,esk4_0,esk2_0))
    | ~ m1_subset_1(X1,esk3_0)
    | ~ r2_hidden(k4_tarski(X1,esk5_0),esk4_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_41,plain,(
    ! [X42,X43] :
      ( ~ r2_hidden(X42,X43)
      | m1_subset_1(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk3_0,esk1_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( r2_hidden(esk7_4(X1,X2,k9_relat_1(X1,X2),X3),X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk5_0),esk4_0)
    | r2_hidden(esk5_0,k9_relat_1(esk4_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_46,plain,(
    ! [X59,X60,X61] :
      ( ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
      | v1_relat_1(X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k9_relat_1(esk4_0,esk2_0))
    | ~ r2_hidden(k4_tarski(X1,esk5_0),esk4_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk4_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk7_4(esk4_0,esk2_0,k9_relat_1(esk4_0,esk2_0),esk5_0),esk2_0)
    | r2_hidden(k4_tarski(esk6_0,esk5_0),esk4_0)
    | ~ v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( r2_hidden(k4_tarski(esk7_4(X1,X2,X3,X4),X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k9_relat_1(esk4_0,esk2_0))
    | ~ r2_hidden(k4_tarski(X1,esk5_0),esk4_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk7_4(esk4_0,esk2_0,k9_relat_1(esk4_0,esk2_0),esk5_0),esk2_0)
    | r2_hidden(k4_tarski(esk6_0,esk5_0),esk4_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,plain,
    ( r2_hidden(k4_tarski(esk7_4(X1,X2,k9_relat_1(X1,X2),X3),X3),X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk5_0),esk4_0)
    | ~ r2_hidden(k4_tarski(X1,esk5_0),esk4_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk7_4(esk4_0,esk2_0,k9_relat_1(esk4_0,esk2_0),esk5_0),esk2_0)
    | r2_hidden(k4_tarski(esk6_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_21])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk6_0,esk2_0)
    | r2_hidden(esk5_0,k7_relset_1(esk3_0,esk1_0,esk4_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_4(esk4_0,esk2_0,k9_relat_1(esk4_0,esk2_0),esk5_0),esk5_0),esk4_0)
    | r2_hidden(k4_tarski(esk6_0,esk5_0),esk4_0)
    | ~ v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_45])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk5_0),esk4_0)
    | ~ r2_hidden(k4_tarski(esk7_4(esk4_0,esk2_0,k9_relat_1(esk4_0,esk2_0),esk5_0),esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk5_0,k9_relat_1(esk4_0,esk2_0))
    | r2_hidden(esk6_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_39])).

cnf(c_0_62,plain,
    ( r2_hidden(X2,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X5 != k9_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk5_0),esk4_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_51]),c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk7_4(esk4_0,esk2_0,k9_relat_1(esk4_0,esk2_0),esk5_0),esk2_0)
    | r2_hidden(esk6_0,esk2_0)
    | ~ v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_4(esk4_0,esk2_0,k9_relat_1(esk4_0,esk2_0),esk5_0),esk5_0),esk4_0)
    | r2_hidden(esk6_0,esk2_0)
    | ~ v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_61])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_21])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk7_4(esk4_0,esk2_0,k9_relat_1(esk4_0,esk2_0),esk5_0),esk2_0)
    | r2_hidden(esk6_0,esk2_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_51])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_4(esk4_0,esk2_0,k9_relat_1(esk4_0,esk2_0),esk5_0),esk5_0),esk4_0)
    | r2_hidden(esk6_0,esk2_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_51])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk5_0,k9_relat_1(esk4_0,X1))
    | ~ v1_relat_1(esk4_0)
    | ~ r2_hidden(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk6_0,esk2_0)
    | ~ r2_hidden(k4_tarski(X1,esk5_0),esk4_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk7_4(esk4_0,esk2_0,k9_relat_1(esk4_0,esk2_0),esk5_0),esk2_0)
    | r2_hidden(esk6_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_21])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_4(esk4_0,esk2_0,k9_relat_1(esk4_0,esk2_0),esk5_0),esk5_0),esk4_0)
    | r2_hidden(esk6_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_21])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk5_0,k9_relat_1(esk4_0,X1))
    | ~ r2_hidden(esk6_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_51])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk6_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk5_0,k9_relat_1(esk4_0,esk2_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk5_0,k9_relat_1(esk4_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_21])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk5_0),esk4_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_77])])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_75]),c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
