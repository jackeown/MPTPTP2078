%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relset_1__t36_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:10 EDT 2019

% Result     : Theorem 25.49s
% Output     : CNFRefutation 25.49s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 151 expanded)
%              Number of clauses        :   31 (  65 expanded)
%              Number of leaves         :   10 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  168 ( 510 expanded)
%              Number of equality atoms :   21 (  48 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X2,X3)
       => r2_relset_1(X1,X2,k6_relset_1(X1,X2,X3,X4),X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t36_relset_1.p',t36_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t36_relset_1.p',cc1_relset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t36_relset_1.p',t4_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t36_relset_1.p',t5_subset)).

fof(d12_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( X3 = k8_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t36_relset_1.p',d12_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t36_relset_1.p',t3_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t36_relset_1.p',t2_subset)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t36_relset_1.p',t106_zfmisc_1)).

fof(redefinition_k6_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k6_relset_1(X1,X2,X3,X4) = k8_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t36_relset_1.p',redefinition_k6_relset_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t36_relset_1.p',redefinition_r2_relset_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ( r1_tarski(X2,X3)
         => r2_relset_1(X1,X2,k6_relset_1(X1,X2,X3,X4),X4) ) ) ),
    inference(assume_negation,[status(cth)],[t36_relset_1])).

fof(c_0_11,plain,(
    ! [X74,X75,X76] :
      ( ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X75)))
      | v1_relat_1(X76) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r1_tarski(esk2_0,esk3_0)
    & ~ r2_relset_1(esk1_0,esk2_0,k6_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X63,X64,X65] :
      ( ~ r2_hidden(X63,X64)
      | ~ m1_subset_1(X64,k1_zfmisc_1(X65))
      | m1_subset_1(X63,X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_14,plain,(
    ! [X66,X67,X68] :
      ( ~ r2_hidden(X66,X67)
      | ~ m1_subset_1(X67,k1_zfmisc_1(X68))
      | ~ v1_xboole_0(X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_15,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X16,X12)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k8_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(X15,X16),X13)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k8_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(X18,X12)
        | ~ r2_hidden(k4_tarski(X17,X18),X13)
        | r2_hidden(k4_tarski(X17,X18),X14)
        | X14 != k8_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(esk5_3(X12,X13,X14),esk6_3(X12,X13,X14)),X14)
        | ~ r2_hidden(esk6_3(X12,X13,X14),X12)
        | ~ r2_hidden(k4_tarski(esk5_3(X12,X13,X14),esk6_3(X12,X13,X14)),X13)
        | X14 = k8_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk6_3(X12,X13,X14),X12)
        | r2_hidden(k4_tarski(esk5_3(X12,X13,X14),esk6_3(X12,X13,X14)),X14)
        | X14 = k8_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk5_3(X12,X13,X14),esk6_3(X12,X13,X14)),X13)
        | r2_hidden(k4_tarski(esk5_3(X12,X13,X14),esk6_3(X12,X13,X14)),X14)
        | X14 = k8_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).

cnf(c_0_16,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X61,X62] :
      ( ( ~ m1_subset_1(X61,k1_zfmisc_1(X62))
        | r1_tarski(X61,X62) )
      & ( ~ r1_tarski(X61,X62)
        | m1_subset_1(X61,k1_zfmisc_1(X62)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_19,plain,(
    ! [X59,X60] :
      ( ~ m1_subset_1(X59,X60)
      | v1_xboole_0(X60)
      | r2_hidden(X59,X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk6_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk6_3(X1,X2,X3)),X3)
    | X3 = k8_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_26,plain,(
    ! [X53,X54,X55,X56] :
      ( ( r2_hidden(X53,X55)
        | ~ r2_hidden(k4_tarski(X53,X54),k2_zfmisc_1(X55,X56)) )
      & ( r2_hidden(X54,X56)
        | ~ r2_hidden(k4_tarski(X53,X54),k2_zfmisc_1(X55,X56)) )
      & ( ~ r2_hidden(X53,X55)
        | ~ r2_hidden(X54,X56)
        | r2_hidden(k4_tarski(X53,X54),k2_zfmisc_1(X55,X56)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( esk4_0 = k8_relat_1(X1,X2)
    | r2_hidden(k4_tarski(esk5_3(X1,X2,esk4_0),esk6_3(X1,X2,esk4_0)),esk4_0)
    | r2_hidden(k4_tarski(esk5_3(X1,X2,esk4_0),esk6_3(X1,X2,esk4_0)),X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

fof(c_0_34,plain,(
    ! [X37,X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k6_relset_1(X37,X38,X39,X40) = k8_relat_1(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_relset_1])])).

cnf(c_0_35,plain,
    ( X3 = k8_relat_1(X1,X2)
    | ~ r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk6_3(X1,X2,X3)),X3)
    | ~ r2_hidden(esk6_3(X1,X2,X3),X1)
    | ~ r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk6_3(X1,X2,X3)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( k8_relat_1(X1,esk4_0) = esk4_0
    | r2_hidden(k4_tarski(esk5_3(X1,esk4_0,esk4_0),esk6_3(X1,esk4_0,esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(k4_tarski(X2,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk2_0,k6_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,plain,
    ( k6_relset_1(X2,X3,X4,X1) = k8_relat_1(X4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k8_relat_1(X1,esk4_0) = esk4_0
    | ~ r2_hidden(esk6_3(X1,esk4_0,esk4_0),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_23])]),c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_37]),c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k8_relat_1(X1,esk4_0) = esk4_0
    | r2_hidden(esk6_3(X1,esk4_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_36])).

fof(c_0_45,plain,(
    ! [X41,X42,X43,X44] :
      ( ( ~ r2_relset_1(X41,X42,X43,X44)
        | X43 = X44
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( X43 != X44
        | r2_relset_1(X41,X42,X43,X44)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk2_0,k8_relat_1(esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_17])])).

cnf(c_0_47,negated_conjecture,
    ( k8_relat_1(esk3_0,esk4_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_48,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk2_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
