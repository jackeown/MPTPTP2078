%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:16 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 255 expanded)
%              Number of clauses        :   37 ( 108 expanded)
%              Number of leaves         :   11 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  184 (1040 expanded)
%              Number of equality atoms :   12 (  32 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
             => ! [X4] :
                  ( r2_hidden(X4,k2_relset_1(X2,X1,X3))
                <=> ? [X5] :
                      ( m1_subset_1(X5,X2)
                      & r2_hidden(k4_tarski(X5,X4),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
               => ! [X4] :
                    ( r2_hidden(X4,k2_relset_1(X2,X1,X3))
                  <=> ? [X5] :
                        ( m1_subset_1(X5,X2)
                        & r2_hidden(k4_tarski(X5,X4),X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_relset_1])).

fof(c_0_12,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k2_relset_1(X31,X32,X33) = k2_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_13,negated_conjecture,(
    ! [X38] :
      ( ~ v1_xboole_0(esk2_0)
      & ~ v1_xboole_0(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
      & ( ~ r2_hidden(esk5_0,k2_relset_1(esk3_0,esk2_0,esk4_0))
        | ~ m1_subset_1(X38,esk3_0)
        | ~ r2_hidden(k4_tarski(X38,esk5_0),esk4_0) )
      & ( m1_subset_1(esk6_0,esk3_0)
        | r2_hidden(esk5_0,k2_relset_1(esk3_0,esk2_0,esk4_0)) )
      & ( r2_hidden(k4_tarski(esk6_0,esk5_0),esk4_0)
        | r2_hidden(esk5_0,k2_relset_1(esk3_0,esk2_0,esk4_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])])).

fof(c_0_14,plain,(
    ! [X13,X14,X15,X17] :
      ( ( r2_hidden(esk1_3(X13,X14,X15),k1_relat_1(X15))
        | ~ r2_hidden(X13,k9_relat_1(X15,X14))
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk1_3(X13,X14,X15),X13),X15)
        | ~ r2_hidden(X13,k9_relat_1(X15,X14))
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X14)
        | ~ r2_hidden(X13,k9_relat_1(X15,X14))
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(X17,k1_relat_1(X15))
        | ~ r2_hidden(k4_tarski(X17,X13),X15)
        | ~ r2_hidden(X17,X14)
        | r2_hidden(X13,k9_relat_1(X15,X14))
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_15,plain,(
    ! [X22,X23,X24] :
      ( ( r2_hidden(X22,k1_relat_1(X24))
        | ~ r2_hidden(k4_tarski(X22,X23),X24)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(X23,k2_relat_1(X24))
        | ~ r2_hidden(k4_tarski(X22,X23),X24)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

fof(c_0_16,plain,(
    ! [X28,X29,X30] :
      ( ( v4_relat_1(X30,X28)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( v5_relat_1(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_17,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | v1_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_18,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(X3,k9_relat_1(X2,X4))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ v4_relat_1(X21,X20)
      | X21 = k7_relat_1(X21,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_23,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k2_relset_1(esk3_0,esk2_0,esk4_0))
    | ~ m1_subset_1(X1,esk3_0)
    | ~ r2_hidden(k4_tarski(X1,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( k2_relset_1(esk3_0,esk2_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk5_0),esk4_0)
    | r2_hidden(esk5_0,k2_relset_1(esk3_0,esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_30,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | k2_relat_1(k7_relat_1(X19,X18)) = k9_relat_1(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_31,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( v4_relat_1(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_19])).

fof(c_0_34,plain,(
    ! [X8,X9,X10] :
      ( ~ r2_hidden(X8,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X10))
      | m1_subset_1(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_35,plain,(
    ! [X6,X7] :
      ( ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | m1_subset_1(X6,k1_zfmisc_1(X7)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk5_0),esk4_0)
    | ~ r2_hidden(esk5_0,k2_relat_1(esk4_0))
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk5_0),esk4_0)
    | r2_hidden(esk5_0,k2_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk1_3(X1,X4,X2),X3)
    | ~ r2_hidden(X1,k9_relat_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k9_relat_1(esk4_0,X1))
    | ~ r2_hidden(esk5_0,k2_relat_1(esk4_0))
    | ~ m1_subset_1(esk1_3(esk5_0,X1,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_29]),c_0_33])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk5_0,k2_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_33])])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k9_relat_1(X2,k1_relat_1(X2)))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k9_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k9_relat_1(esk4_0,esk3_0) = k2_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_33])])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k9_relat_1(esk4_0,X1))
    | ~ m1_subset_1(esk1_3(esk5_0,X1,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(X1,k9_relat_1(esk4_0,k1_relat_1(esk4_0)))
    | ~ r2_hidden(X1,k2_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_33])])).

cnf(c_0_53,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X4)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( ~ m1_subset_1(esk1_3(esk5_0,k1_relat_1(esk4_0),esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_46])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk1_3(X1,k1_relat_1(esk4_0),esk4_0),X2)
    | ~ r2_hidden(X1,k2_relat_1(esk4_0))
    | ~ r1_tarski(k1_relat_1(esk4_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_52]),c_0_33])])).

fof(c_0_56,plain,(
    ! [X11,X12] :
      ( ( ~ v4_relat_1(X12,X11)
        | r1_tarski(k1_relat_1(X12),X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r1_tarski(k1_relat_1(X12),X11)
        | v4_relat_1(X12,X11)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_46])])).

cnf(c_0_58,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_32]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:24:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t48_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>![X4]:(r2_hidden(X4,k2_relset_1(X2,X1,X3))<=>?[X5]:(m1_subset_1(X5,X2)&r2_hidden(k4_tarski(X5,X4),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relset_1)).
% 0.19/0.37  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.37  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.19/0.37  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 0.19/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.37  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.19/0.37  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.19/0.37  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.37  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.19/0.37  fof(c_0_11, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>![X4]:(r2_hidden(X4,k2_relset_1(X2,X1,X3))<=>?[X5]:(m1_subset_1(X5,X2)&r2_hidden(k4_tarski(X5,X4),X3))))))), inference(assume_negation,[status(cth)],[t48_relset_1])).
% 0.19/0.37  fof(c_0_12, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k2_relset_1(X31,X32,X33)=k2_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.37  fof(c_0_13, negated_conjecture, ![X38]:(~v1_xboole_0(esk2_0)&(~v1_xboole_0(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))&((~r2_hidden(esk5_0,k2_relset_1(esk3_0,esk2_0,esk4_0))|(~m1_subset_1(X38,esk3_0)|~r2_hidden(k4_tarski(X38,esk5_0),esk4_0)))&((m1_subset_1(esk6_0,esk3_0)|r2_hidden(esk5_0,k2_relset_1(esk3_0,esk2_0,esk4_0)))&(r2_hidden(k4_tarski(esk6_0,esk5_0),esk4_0)|r2_hidden(esk5_0,k2_relset_1(esk3_0,esk2_0,esk4_0)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])])).
% 0.19/0.37  fof(c_0_14, plain, ![X13, X14, X15, X17]:((((r2_hidden(esk1_3(X13,X14,X15),k1_relat_1(X15))|~r2_hidden(X13,k9_relat_1(X15,X14))|~v1_relat_1(X15))&(r2_hidden(k4_tarski(esk1_3(X13,X14,X15),X13),X15)|~r2_hidden(X13,k9_relat_1(X15,X14))|~v1_relat_1(X15)))&(r2_hidden(esk1_3(X13,X14,X15),X14)|~r2_hidden(X13,k9_relat_1(X15,X14))|~v1_relat_1(X15)))&(~r2_hidden(X17,k1_relat_1(X15))|~r2_hidden(k4_tarski(X17,X13),X15)|~r2_hidden(X17,X14)|r2_hidden(X13,k9_relat_1(X15,X14))|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.19/0.37  fof(c_0_15, plain, ![X22, X23, X24]:((r2_hidden(X22,k1_relat_1(X24))|~r2_hidden(k4_tarski(X22,X23),X24)|~v1_relat_1(X24))&(r2_hidden(X23,k2_relat_1(X24))|~r2_hidden(k4_tarski(X22,X23),X24)|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.19/0.37  fof(c_0_16, plain, ![X28, X29, X30]:((v4_relat_1(X30,X28)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))&(v5_relat_1(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.37  fof(c_0_17, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|v1_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.37  cnf(c_0_18, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_20, plain, (r2_hidden(X3,k9_relat_1(X2,X4))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_21, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  fof(c_0_22, plain, ![X20, X21]:(~v1_relat_1(X21)|~v4_relat_1(X21,X20)|X21=k7_relat_1(X21,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.19/0.37  cnf(c_0_23, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  cnf(c_0_24, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (~r2_hidden(esk5_0,k2_relset_1(esk3_0,esk2_0,esk4_0))|~m1_subset_1(X1,esk3_0)|~r2_hidden(k4_tarski(X1,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (k2_relset_1(esk3_0,esk2_0,esk4_0)=k2_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk5_0),esk4_0)|r2_hidden(esk5_0,k2_relset_1(esk3_0,esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_28, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X1),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.37  cnf(c_0_29, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  fof(c_0_30, plain, ![X18, X19]:(~v1_relat_1(X19)|k2_relat_1(k7_relat_1(X19,X18))=k9_relat_1(X19,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.19/0.37  cnf(c_0_31, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (v4_relat_1(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_19])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_19])).
% 0.19/0.37  fof(c_0_34, plain, ![X8, X9, X10]:(~r2_hidden(X8,X9)|~m1_subset_1(X9,k1_zfmisc_1(X10))|m1_subset_1(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.37  fof(c_0_35, plain, ![X6, X7]:((~m1_subset_1(X6,k1_zfmisc_1(X7))|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|m1_subset_1(X6,k1_zfmisc_1(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk5_0),esk4_0)|~r2_hidden(esk5_0,k2_relat_1(esk4_0))|~m1_subset_1(X1,esk3_0)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.37  cnf(c_0_37, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk5_0),esk4_0)|r2_hidden(esk5_0,k2_relat_1(esk4_0))), inference(rw,[status(thm)],[c_0_27, c_0_26])).
% 0.19/0.37  cnf(c_0_39, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(esk1_3(X1,X4,X2),X3)|~r2_hidden(X1,k9_relat_1(X2,X4))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.37  cnf(c_0_40, plain, (r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_41, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.19/0.37  cnf(c_0_43, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.37  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (~r2_hidden(esk5_0,k9_relat_1(esk4_0,X1))|~r2_hidden(esk5_0,k2_relat_1(esk4_0))|~m1_subset_1(esk1_3(esk5_0,X1,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_29]), c_0_33])])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, (r2_hidden(esk5_0,k2_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_33])])).
% 0.19/0.37  cnf(c_0_47, plain, (r2_hidden(X1,k9_relat_1(X2,k1_relat_1(X2)))|~v1_relat_1(X2)|~r2_hidden(X1,k9_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.37  cnf(c_0_48, negated_conjecture, (k9_relat_1(esk4_0,esk3_0)=k2_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_33])])).
% 0.19/0.37  cnf(c_0_49, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.37  cnf(c_0_50, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_51, negated_conjecture, (~r2_hidden(esk5_0,k9_relat_1(esk4_0,X1))|~m1_subset_1(esk1_3(esk5_0,X1,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])])).
% 0.19/0.37  cnf(c_0_52, negated_conjecture, (r2_hidden(X1,k9_relat_1(esk4_0,k1_relat_1(esk4_0)))|~r2_hidden(X1,k2_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_33])])).
% 0.19/0.37  cnf(c_0_53, plain, (m1_subset_1(esk1_3(X1,X2,X3),X4)|~v1_relat_1(X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.37  cnf(c_0_54, negated_conjecture, (~m1_subset_1(esk1_3(esk5_0,k1_relat_1(esk4_0),esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_46])])).
% 0.19/0.37  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk1_3(X1,k1_relat_1(esk4_0),esk4_0),X2)|~r2_hidden(X1,k2_relat_1(esk4_0))|~r1_tarski(k1_relat_1(esk4_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_52]), c_0_33])])).
% 0.19/0.37  fof(c_0_56, plain, ![X11, X12]:((~v4_relat_1(X12,X11)|r1_tarski(k1_relat_1(X12),X11)|~v1_relat_1(X12))&(~r1_tarski(k1_relat_1(X12),X11)|v4_relat_1(X12,X11)|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.19/0.37  cnf(c_0_57, negated_conjecture, (~r1_tarski(k1_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_46])])).
% 0.19/0.37  cnf(c_0_58, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.37  cnf(c_0_59, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_32]), c_0_33])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 60
% 0.19/0.37  # Proof object clause steps            : 37
% 0.19/0.37  # Proof object formula steps           : 23
% 0.19/0.37  # Proof object conjectures             : 21
% 0.19/0.37  # Proof object clause conjectures      : 18
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 17
% 0.19/0.37  # Proof object initial formulas used   : 11
% 0.19/0.37  # Proof object generating inferences   : 16
% 0.19/0.37  # Proof object simplifying inferences  : 24
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 11
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 23
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 23
% 0.19/0.37  # Processed clauses                    : 74
% 0.19/0.37  # ...of these trivial                  : 1
% 0.19/0.37  # ...subsumed                          : 6
% 0.19/0.37  # ...remaining for further processing  : 67
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 6
% 0.19/0.37  # Generated clauses                    : 94
% 0.19/0.37  # ...of the previous two non-trivial   : 88
% 0.19/0.37  # Contextual simplify-reflections      : 1
% 0.19/0.37  # Paramodulations                      : 94
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 61
% 0.19/0.37  #    Positive orientable unit clauses  : 9
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 6
% 0.19/0.37  #    Non-unit-clauses                  : 46
% 0.19/0.37  # Current number of unprocessed clauses: 32
% 0.19/0.37  # ...number of literals in the above   : 117
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 6
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 229
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 204
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 7
% 0.19/0.37  # Unit Clause-clause subsumption calls : 20
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 2
% 0.19/0.37  # BW rewrite match successes           : 2
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 3274
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.031 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.035 s
% 0.19/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
