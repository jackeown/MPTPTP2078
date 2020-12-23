%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t49_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:46 EDT 2019

% Result     : Theorem 23.23s
% Output     : CNFRefutation 23.23s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 446 expanded)
%              Number of clauses        :   52 ( 187 expanded)
%              Number of leaves         :   11 ( 112 expanded)
%              Depth                    :   20
%              Number of atoms          :  196 (1685 expanded)
%              Number of equality atoms :   46 ( 599 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & k8_relset_1(X1,X2,X3,k1_tarski(X4)) = k1_xboole_0 )
      <=> k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',t49_funct_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',d10_xboole_0)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',redefinition_k8_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',t3_subset)).

fof(t142_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k2_relat_1(X2))
      <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',t142_funct_1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',dt_k2_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',redefinition_k2_relset_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',t6_boole)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',cc1_relset_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',dt_o_0_0_xboole_0)).

fof(t143_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & k10_relat_1(X2,k1_tarski(X3)) = k1_xboole_0 )
       => r1_tarski(X1,k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',t143_funct_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ! [X4] :
              ~ ( r2_hidden(X4,X2)
                & k8_relset_1(X1,X2,X3,k1_tarski(X4)) = k1_xboole_0 )
        <=> k2_relset_1(X1,X2,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t49_funct_2])).

fof(c_0_12,negated_conjecture,(
    ! [X9] :
      ( v1_funct_1(esk3_0)
      & v1_funct_2(esk3_0,esk1_0,esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
      & ( r2_hidden(esk4_0,esk2_0)
        | k2_relset_1(esk1_0,esk2_0,esk3_0) != esk2_0 )
      & ( k8_relset_1(esk1_0,esk2_0,esk3_0,k1_tarski(esk4_0)) = k1_xboole_0
        | k2_relset_1(esk1_0,esk2_0,esk3_0) != esk2_0 )
      & ( ~ r2_hidden(X9,esk2_0)
        | k8_relset_1(esk1_0,esk2_0,esk3_0,k1_tarski(X9)) != k1_xboole_0
        | k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])])).

fof(c_0_13,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_14,plain,(
    ! [X26,X27,X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k8_relset_1(X26,X27,X28,X29) = k10_relat_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0)
    | k2_relset_1(esk1_0,esk2_0,esk3_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X39,X40] :
      ( ( ~ m1_subset_1(X39,k1_zfmisc_1(X40))
        | r1_tarski(X39,X40) )
      & ( ~ r1_tarski(X39,X40)
        | m1_subset_1(X39,k1_zfmisc_1(X40)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_18,plain,(
    ! [X30,X31] :
      ( ( ~ r2_hidden(X30,k2_relat_1(X31))
        | k10_relat_1(X31,k1_tarski(X30)) != k1_xboole_0
        | ~ v1_relat_1(X31) )
      & ( k10_relat_1(X31,k1_tarski(X30)) = k1_xboole_0
        | r2_hidden(X30,k2_relat_1(X31))
        | ~ v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_funct_1])])])).

cnf(c_0_19,negated_conjecture,
    ( k8_relset_1(esk1_0,esk2_0,esk3_0,k1_tarski(esk4_0)) = k1_xboole_0
    | k2_relset_1(esk1_0,esk2_0,esk3_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0)
    | ~ r1_tarski(k2_relset_1(esk1_0,esk2_0,esk3_0),esk2_0)
    | ~ r1_tarski(esk2_0,k2_relset_1(esk1_0,esk2_0,esk3_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | m1_subset_1(k2_relset_1(X14,X15,X16),k1_zfmisc_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k2_relat_1(X2))
    | k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( k10_relat_1(esk3_0,k1_tarski(esk4_0)) = k1_xboole_0
    | k2_relset_1(esk1_0,esk2_0,esk3_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

fof(c_0_27,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k2_relset_1(X23,X24,X25) = k2_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0)
    | ~ r1_tarski(esk2_0,k2_relset_1(esk1_0,esk2_0,esk3_0))
    | ~ m1_subset_1(k2_relset_1(esk1_0,esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    | ~ r2_hidden(X1,esk2_0)
    | k8_relset_1(esk1_0,esk2_0,esk3_0,k1_tarski(X1)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_31,plain,(
    ! [X47] :
      ( ~ v1_xboole_0(X47)
      | X47 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_32,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) != esk2_0
    | ~ v1_relat_1(esk3_0)
    | ~ r2_hidden(esk4_0,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0)
    | ~ r1_tarski(esk2_0,k2_relset_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_21])])).

cnf(c_0_35,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    | k10_relat_1(esk3_0,k1_tarski(X1)) != k1_xboole_0
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_20]),c_0_21])])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k2_relat_1(esk3_0) != esk2_0
    | ~ v1_relat_1(esk3_0)
    | ~ r2_hidden(esk4_0,k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_21])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0)
    | ~ r1_tarski(esk2_0,k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_21])])).

cnf(c_0_39,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    | ~ v1_xboole_0(k10_relat_1(esk3_0,k1_tarski(X1)))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_relat_1(esk3_0)
    | ~ r1_tarski(esk2_0,k2_relat_1(esk3_0))
    | ~ r1_tarski(k2_relat_1(esk3_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_16])]),c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0
    | ~ v1_xboole_0(k10_relat_1(esk3_0,k1_tarski(X1)))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_39]),c_0_21])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_40])).

fof(c_0_44,plain,(
    ! [X52,X53,X54] :
      ( ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | v1_relat_1(X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_relat_1(esk3_0)
    | ~ v1_xboole_0(k10_relat_1(esk3_0,k1_tarski(X1)))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_46,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_xboole_0(k10_relat_1(esk3_0,k1_tarski(X1)))
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_48,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_xboole_0(k10_relat_1(esk3_0,k1_tarski(X1)))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_21])).

cnf(c_0_50,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_36]),c_0_48])])).

cnf(c_0_51,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) != esk2_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_26]),c_0_50])]),c_0_15])).

fof(c_0_52,plain,(
    ! [X32,X33] :
      ( ( r2_hidden(esk6_2(X32,X33),X32)
        | r1_tarski(X32,k2_relat_1(X33))
        | ~ v1_relat_1(X33) )
      & ( k10_relat_1(X33,k1_tarski(esk6_2(X32,X33))) = k1_xboole_0
        | r1_tarski(X32,k2_relat_1(X33))
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_funct_1])])])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k2_relset_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tarski(k2_relset_1(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_16])])).

cnf(c_0_54,negated_conjecture,
    ( k2_relat_1(esk3_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_33]),c_0_21])])).

cnf(c_0_55,plain,
    ( r2_hidden(esk6_2(X1,X2),X1)
    | r1_tarski(X1,k2_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(esk1_0,esk2_0,esk3_0),esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_relset_1(esk1_0,esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_23])).

cnf(c_0_57,plain,
    ( k10_relat_1(X1,k1_tarski(esk6_2(X2,X1))) = k1_xboole_0
    | r1_tarski(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k2_relat_1(esk3_0))
    | ~ r1_tarski(k2_relat_1(esk3_0),esk2_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_16])])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k2_relat_1(X2))
    | r2_hidden(esk6_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_46])).

cnf(c_0_60,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_33])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk3_0),esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_relat_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_33]),c_0_21])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(X1,k2_relat_1(esk3_0))
    | ~ v1_relat_1(esk3_0)
    | ~ r2_hidden(esk6_2(X1,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_57]),c_0_50])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk6_2(esk2_0,esk3_0),esk2_0)
    | ~ r1_tarski(k2_relat_1(esk3_0),esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_21])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tarski(X1,k1_zfmisc_1(k2_relat_1(esk3_0)))
    | ~ r1_tarski(k1_zfmisc_1(k2_relat_1(esk3_0)),X1)
    | ~ r1_tarski(k2_relat_1(esk3_0),esk2_0)
    | ~ m1_subset_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_16])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(X1,k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X2,esk3_0)
    | ~ r1_tarski(esk3_0,X2)
    | ~ r2_hidden(esk6_2(X1,X2),esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_16])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk6_2(esk2_0,esk3_0),esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_23]),c_0_64])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(X1,k1_zfmisc_1(k2_relat_1(esk3_0)))
    | ~ r1_tarski(k1_zfmisc_1(k2_relat_1(esk3_0)),X1)
    | ~ m1_subset_1(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_23]),c_0_64])])).

cnf(c_0_69,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk2_0,k2_relat_1(esk3_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_43])]),c_0_46])).

cnf(c_0_71,negated_conjecture,
    ( ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_relat_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_43]),c_0_43])])).

cnf(c_0_72,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_21,c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
