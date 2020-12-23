%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:49 EST 2020

% Result     : Theorem 8.41s
% Output     : CNFRefutation 8.41s
% Verified   : 
% Statistics : Number of formulae       :   90 (138206 expanded)
%              Number of clauses        :   71 (55974 expanded)
%              Number of leaves         :    9 (33210 expanded)
%              Depth                    :   23
%              Number of atoms          :  266 (573677 expanded)
%              Number of equality atoms :   47 (63009 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t54_relset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
         => ( ! [X4] :
                ( r2_hidden(X4,X1)
               => k11_relat_1(X2,X4) = k11_relat_1(X3,X4) )
           => r2_relset_1(X1,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relset_1)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(d3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( r2_relset_1(X1,X2,X3,X4)
          <=> ! [X5] :
                ( m1_subset_1(X5,X1)
               => ! [X6] :
                    ( m1_subset_1(X6,X2)
                   => ( r2_hidden(k4_tarski(X5,X6),X3)
                    <=> r2_hidden(k4_tarski(X5,X6),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
           => ( ! [X4] :
                  ( r2_hidden(X4,X1)
                 => k11_relat_1(X2,X4) = k11_relat_1(X3,X4) )
             => r2_relset_1(X1,X1,X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t54_relset_1])).

fof(c_0_10,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_xboole_0(X17)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | v1_xboole_0(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

fof(c_0_11,negated_conjecture,(
    ! [X35] :
      ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
      & ( ~ r2_hidden(X35,esk3_0)
        | k11_relat_1(esk4_0,X35) = k11_relat_1(esk5_0,X35) )
      & ~ r2_relset_1(esk3_0,esk3_0,esk4_0,esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(k4_tarski(X24,X25),X22)
        | r2_hidden(k4_tarski(X24,X25),X23)
        | ~ m1_subset_1(X25,X21)
        | ~ m1_subset_1(X24,X20)
        | ~ r2_relset_1(X20,X21,X22,X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( ~ r2_hidden(k4_tarski(X24,X25),X23)
        | r2_hidden(k4_tarski(X24,X25),X22)
        | ~ m1_subset_1(X25,X21)
        | ~ m1_subset_1(X24,X20)
        | ~ r2_relset_1(X20,X21,X22,X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( m1_subset_1(esk1_4(X20,X21,X22,X23),X20)
        | r2_relset_1(X20,X21,X22,X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( m1_subset_1(esk2_4(X20,X21,X22,X23),X21)
        | r2_relset_1(X20,X21,X22,X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( ~ r2_hidden(k4_tarski(esk1_4(X20,X21,X22,X23),esk2_4(X20,X21,X22,X23)),X22)
        | ~ r2_hidden(k4_tarski(esk1_4(X20,X21,X22,X23),esk2_4(X20,X21,X22,X23)),X23)
        | r2_relset_1(X20,X21,X22,X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( r2_hidden(k4_tarski(esk1_4(X20,X21,X22,X23),esk2_4(X20,X21,X22,X23)),X22)
        | r2_hidden(k4_tarski(esk1_4(X20,X21,X22,X23),esk2_4(X20,X21,X22,X23)),X23)
        | r2_relset_1(X20,X21,X22,X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relset_1])])])])])).

cnf(c_0_13,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X9,X8)
        | r2_hidden(X9,X8)
        | v1_xboole_0(X8) )
      & ( ~ r2_hidden(X9,X8)
        | m1_subset_1(X9,X8)
        | v1_xboole_0(X8) )
      & ( ~ m1_subset_1(X9,X8)
        | v1_xboole_0(X9)
        | ~ v1_xboole_0(X8) )
      & ( ~ v1_xboole_0(X9)
        | m1_subset_1(X9,X8)
        | ~ v1_xboole_0(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),X1)
    | r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,X1,esk5_0)
    | m1_subset_1(esk1_4(esk3_0,esk3_0,X1,esk5_0),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_relset_1(esk3_0,esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(esk1_4(X1,X2,X3,X4),esk2_4(X1,X2,X3,X4)),X3)
    | r2_hidden(k4_tarski(esk1_4(X1,X2,X3,X4),esk2_4(X1,X2,X3,X4)),X4)
    | r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_23,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | v1_relat_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_24,plain,(
    ! [X12,X13] : v1_relat_1(k2_zfmisc_1(X12,X13)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_25,plain,(
    ! [X7] :
      ( ~ v1_xboole_0(X7)
      | X7 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | v1_xboole_0(esk5_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

fof(c_0_28,plain,(
    ! [X14,X15,X16] :
      ( ( ~ r2_hidden(k4_tarski(X14,X15),X16)
        | r2_hidden(X15,k11_relat_1(X16,X14))
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(X15,k11_relat_1(X16,X14))
        | r2_hidden(k4_tarski(X14,X15),X16)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

cnf(c_0_29,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,X1,esk5_0)
    | r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,X1,esk5_0),esk2_4(esk3_0,esk3_0,X1,esk5_0)),esk5_0)
    | r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,X1,esk5_0),esk2_4(esk3_0,esk3_0,X1,esk5_0)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_14])).

cnf(c_0_30,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk3_0)
    | v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk2_4(esk3_0,esk3_0,esk4_0,esk5_0)),esk4_0)
    | r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk2_4(esk3_0,esk3_0,esk4_0,esk5_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_20]),c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_14]),c_0_31])])).

cnf(c_0_37,negated_conjecture,
    ( k11_relat_1(esk4_0,X1) = k11_relat_1(esk5_0,X1)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk2_4(esk3_0,esk3_0,esk4_0,esk5_0)),esk4_0)
    | r2_hidden(esk2_4(esk3_0,esk3_0,esk4_0,esk5_0),k11_relat_1(esk5_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_40,negated_conjecture,
    ( k11_relat_1(esk5_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0)) = k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0))
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk2_4(esk3_0,esk3_0,esk4_0,esk5_0),k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0)))
    | r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk2_4(esk3_0,esk3_0,esk4_0,esk5_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_20]),c_0_31])])).

cnf(c_0_44,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_20])).

cnf(c_0_45,plain,
    ( r2_relset_1(X1,X2,X3,X4)
    | ~ r2_hidden(k4_tarski(esk1_4(X1,X2,X3,X4),esk2_4(X1,X2,X3,X4)),X3)
    | ~ r2_hidden(k4_tarski(esk1_4(X1,X2,X3,X4),esk2_4(X1,X2,X3,X4)),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk2_4(esk3_0,esk3_0,esk4_0,esk5_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | v1_xboole_0(esk4_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_18])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,X1,esk5_0)
    | ~ r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,X1,esk5_0),esk2_4(esk3_0,esk3_0,X1,esk5_0)),esk5_0)
    | ~ r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,X1,esk5_0),esk2_4(esk3_0,esk3_0,X1,esk5_0)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_14])).

cnf(c_0_50,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),X1),esk5_0)
    | ~ r2_hidden(X1,k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_40]),c_0_36])])).

cnf(c_0_51,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk2_4(esk3_0,esk3_0,esk4_0,esk5_0),k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_46]),c_0_43])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk3_0)
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_27])).

cnf(c_0_53,negated_conjecture,
    ( k11_relat_1(esk5_0,X1) = k11_relat_1(esk4_0,X1)
    | esk3_0 = k1_xboole_0
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk2_4(esk3_0,esk3_0,esk4_0,esk5_0)),esk5_0)
    | ~ r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk2_4(esk3_0,esk3_0,esk4_0,esk5_0)),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_20]),c_0_21])).

cnf(c_0_55,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk2_4(esk3_0,esk3_0,esk4_0,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( k11_relat_1(esk5_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0)) = k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0))
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_27])).

cnf(c_0_58,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( k11_relat_1(esk5_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0)) = k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0))
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)) = k11_relat_1(k1_xboole_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0))
    | esk3_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58]),c_0_58]),c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)) = k11_relat_1(k1_xboole_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0))
    | esk4_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_58]),c_0_58]),c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),X1),esk4_0)
    | ~ r2_hidden(X1,k11_relat_1(k1_xboole_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_60]),c_0_43])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),k11_relat_1(k1_xboole_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)))
    | r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),X1),esk4_0)
    | ~ r2_hidden(X1,k11_relat_1(k1_xboole_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_61]),c_0_43])])).

cnf(c_0_65,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),X1),esk5_0)
    | ~ r2_hidden(X1,k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_57]),c_0_36])])).

cnf(c_0_66,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),X1),k1_xboole_0)
    | ~ r2_hidden(X1,k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_58]),c_0_58]),c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_66]),c_0_43])])).

fof(c_0_70,plain,(
    ! [X28,X29,X30,X31] :
      ( ( ~ r2_relset_1(X28,X29,X30,X31)
        | X30 = X31
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( X30 != X31
        | r2_relset_1(X28,X29,X30,X31)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_71,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_67]),c_0_43])])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)),k1_xboole_0)
    | ~ r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_58])).

cnf(c_0_73,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),k11_relat_1(k1_xboole_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_61])).

cnf(c_0_76,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_66])).

cnf(c_0_77,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk2_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0),k11_relat_1(k1_xboole_0,esk1_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76]),c_0_76]),c_0_76]),c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_58])).

cnf(c_0_80,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_14])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_relset_1(esk3_0,esk3_0,esk4_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_21,c_0_58])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0),esk2_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0)),k1_xboole_0)
    | ~ r2_hidden(k4_tarski(esk1_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0),esk2_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0)),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_76]),c_0_76]),c_0_76]),c_0_76]),c_0_76]),c_0_76]),c_0_76]),c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0),esk2_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_78]),c_0_79])])).

cnf(c_0_84,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0),esk2_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0)),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_76]),c_0_76]),c_0_76]),c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_58]),c_0_58])).

cnf(c_0_86,negated_conjecture,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_76]),c_0_76])).

cnf(c_0_87,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_76]),c_0_76])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87]),c_0_88])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:01:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 8.41/8.61  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 8.41/8.61  # and selection function SelectCQIArNXTEqFirst.
% 8.41/8.61  #
% 8.41/8.61  # Preprocessing time       : 0.028 s
% 8.41/8.61  # Presaturation interreduction done
% 8.41/8.61  
% 8.41/8.61  # Proof found!
% 8.41/8.61  # SZS status Theorem
% 8.41/8.61  # SZS output start CNFRefutation
% 8.41/8.61  fof(t54_relset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>(![X4]:(r2_hidden(X4,X1)=>k11_relat_1(X2,X4)=k11_relat_1(X3,X4))=>r2_relset_1(X1,X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relset_1)).
% 8.41/8.61  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 8.41/8.61  fof(d3_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(r2_relset_1(X1,X2,X3,X4)<=>![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X2)=>(r2_hidden(k4_tarski(X5,X6),X3)<=>r2_hidden(k4_tarski(X5,X6),X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relset_1)).
% 8.41/8.61  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 8.41/8.61  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.41/8.61  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.41/8.61  fof(t6_boole, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 8.41/8.61  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 8.41/8.61  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.41/8.61  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>(![X4]:(r2_hidden(X4,X1)=>k11_relat_1(X2,X4)=k11_relat_1(X3,X4))=>r2_relset_1(X1,X1,X2,X3))))), inference(assume_negation,[status(cth)],[t54_relset_1])).
% 8.41/8.61  fof(c_0_10, plain, ![X17, X18, X19]:(~v1_xboole_0(X17)|(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|v1_xboole_0(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 8.41/8.61  fof(c_0_11, negated_conjecture, ![X35]:(m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))&((~r2_hidden(X35,esk3_0)|k11_relat_1(esk4_0,X35)=k11_relat_1(esk5_0,X35))&~r2_relset_1(esk3_0,esk3_0,esk4_0,esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 8.41/8.61  fof(c_0_12, plain, ![X20, X21, X22, X23, X24, X25]:(((~r2_hidden(k4_tarski(X24,X25),X22)|r2_hidden(k4_tarski(X24,X25),X23)|~m1_subset_1(X25,X21)|~m1_subset_1(X24,X20)|~r2_relset_1(X20,X21,X22,X23)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(~r2_hidden(k4_tarski(X24,X25),X23)|r2_hidden(k4_tarski(X24,X25),X22)|~m1_subset_1(X25,X21)|~m1_subset_1(X24,X20)|~r2_relset_1(X20,X21,X22,X23)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))&((m1_subset_1(esk1_4(X20,X21,X22,X23),X20)|r2_relset_1(X20,X21,X22,X23)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&((m1_subset_1(esk2_4(X20,X21,X22,X23),X21)|r2_relset_1(X20,X21,X22,X23)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&((~r2_hidden(k4_tarski(esk1_4(X20,X21,X22,X23),esk2_4(X20,X21,X22,X23)),X22)|~r2_hidden(k4_tarski(esk1_4(X20,X21,X22,X23),esk2_4(X20,X21,X22,X23)),X23)|r2_relset_1(X20,X21,X22,X23)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(r2_hidden(k4_tarski(esk1_4(X20,X21,X22,X23),esk2_4(X20,X21,X22,X23)),X22)|r2_hidden(k4_tarski(esk1_4(X20,X21,X22,X23),esk2_4(X20,X21,X22,X23)),X23)|r2_relset_1(X20,X21,X22,X23)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relset_1])])])])])).
% 8.41/8.61  cnf(c_0_13, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 8.41/8.61  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 8.41/8.61  fof(c_0_15, plain, ![X8, X9]:(((~m1_subset_1(X9,X8)|r2_hidden(X9,X8)|v1_xboole_0(X8))&(~r2_hidden(X9,X8)|m1_subset_1(X9,X8)|v1_xboole_0(X8)))&((~m1_subset_1(X9,X8)|v1_xboole_0(X9)|~v1_xboole_0(X8))&(~v1_xboole_0(X9)|m1_subset_1(X9,X8)|~v1_xboole_0(X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 8.41/8.61  cnf(c_0_16, plain, (m1_subset_1(esk1_4(X1,X2,X3,X4),X1)|r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 8.41/8.61  cnf(c_0_17, negated_conjecture, (v1_xboole_0(esk5_0)|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 8.41/8.61  cnf(c_0_18, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 8.41/8.61  cnf(c_0_19, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,X1,esk5_0)|m1_subset_1(esk1_4(esk3_0,esk3_0,X1,esk5_0),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_16, c_0_14])).
% 8.41/8.61  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 8.41/8.61  cnf(c_0_21, negated_conjecture, (~r2_relset_1(esk3_0,esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 8.41/8.61  cnf(c_0_22, plain, (r2_hidden(k4_tarski(esk1_4(X1,X2,X3,X4),esk2_4(X1,X2,X3,X4)),X3)|r2_hidden(k4_tarski(esk1_4(X1,X2,X3,X4),esk2_4(X1,X2,X3,X4)),X4)|r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 8.41/8.61  fof(c_0_23, plain, ![X10, X11]:(~v1_relat_1(X10)|(~m1_subset_1(X11,k1_zfmisc_1(X10))|v1_relat_1(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 8.41/8.61  fof(c_0_24, plain, ![X12, X13]:v1_relat_1(k2_zfmisc_1(X12,X13)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 8.41/8.61  fof(c_0_25, plain, ![X7]:(~v1_xboole_0(X7)|X7=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).
% 8.41/8.61  cnf(c_0_26, negated_conjecture, (r2_hidden(X1,esk3_0)|v1_xboole_0(esk5_0)|~m1_subset_1(X1,esk3_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 8.41/8.61  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 8.41/8.61  fof(c_0_28, plain, ![X14, X15, X16]:((~r2_hidden(k4_tarski(X14,X15),X16)|r2_hidden(X15,k11_relat_1(X16,X14))|~v1_relat_1(X16))&(~r2_hidden(X15,k11_relat_1(X16,X14))|r2_hidden(k4_tarski(X14,X15),X16)|~v1_relat_1(X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 8.41/8.61  cnf(c_0_29, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,X1,esk5_0)|r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,X1,esk5_0),esk2_4(esk3_0,esk3_0,X1,esk5_0)),esk5_0)|r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,X1,esk5_0),esk2_4(esk3_0,esk3_0,X1,esk5_0)),X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_22, c_0_14])).
% 8.41/8.61  cnf(c_0_30, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 8.41/8.61  cnf(c_0_31, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 8.41/8.61  cnf(c_0_32, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 8.41/8.61  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk3_0)|v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 8.41/8.61  cnf(c_0_34, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 8.41/8.61  cnf(c_0_35, negated_conjecture, (r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk2_4(esk3_0,esk3_0,esk4_0,esk5_0)),esk4_0)|r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk2_4(esk3_0,esk3_0,esk4_0,esk5_0)),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_20]), c_0_21])).
% 8.41/8.61  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_14]), c_0_31])])).
% 8.41/8.61  cnf(c_0_37, negated_conjecture, (k11_relat_1(esk4_0,X1)=k11_relat_1(esk5_0,X1)|~r2_hidden(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 8.41/8.61  cnf(c_0_38, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 8.41/8.61  cnf(c_0_39, negated_conjecture, (r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk2_4(esk3_0,esk3_0,esk4_0,esk5_0)),esk4_0)|r2_hidden(esk2_4(esk3_0,esk3_0,esk4_0,esk5_0),k11_relat_1(esk5_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 8.41/8.61  cnf(c_0_40, negated_conjecture, (k11_relat_1(esk5_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0))=k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0))|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 8.41/8.61  cnf(c_0_41, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 8.41/8.61  cnf(c_0_42, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk2_4(esk3_0,esk3_0,esk4_0,esk5_0),k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0)))|r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk2_4(esk3_0,esk3_0,esk4_0,esk5_0)),esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 8.41/8.61  cnf(c_0_43, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_20]), c_0_31])])).
% 8.41/8.61  cnf(c_0_44, negated_conjecture, (v1_xboole_0(esk4_0)|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_13, c_0_20])).
% 8.41/8.61  cnf(c_0_45, plain, (r2_relset_1(X1,X2,X3,X4)|~r2_hidden(k4_tarski(esk1_4(X1,X2,X3,X4),esk2_4(X1,X2,X3,X4)),X3)|~r2_hidden(k4_tarski(esk1_4(X1,X2,X3,X4),esk2_4(X1,X2,X3,X4)),X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 8.41/8.61  cnf(c_0_46, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk2_4(esk3_0,esk3_0,esk4_0,esk5_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 8.41/8.61  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,esk3_0)|v1_xboole_0(esk4_0)|~m1_subset_1(X1,esk3_0)), inference(spm,[status(thm)],[c_0_44, c_0_18])).
% 8.41/8.61  cnf(c_0_48, plain, (X1=k1_xboole_0|r2_hidden(X2,X1)|~m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_32, c_0_18])).
% 8.41/8.61  cnf(c_0_49, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,X1,esk5_0)|~r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,X1,esk5_0),esk2_4(esk3_0,esk3_0,X1,esk5_0)),esk5_0)|~r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,X1,esk5_0),esk2_4(esk3_0,esk3_0,X1,esk5_0)),X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_45, c_0_14])).
% 8.41/8.61  cnf(c_0_50, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),X1),esk5_0)|~r2_hidden(X1,k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_40]), c_0_36])])).
% 8.41/8.61  cnf(c_0_51, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk2_4(esk3_0,esk3_0,esk4_0,esk5_0),k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_46]), c_0_43])])).
% 8.41/8.61  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk3_0)|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_47, c_0_27])).
% 8.41/8.61  cnf(c_0_53, negated_conjecture, (k11_relat_1(esk5_0,X1)=k11_relat_1(esk4_0,X1)|esk3_0=k1_xboole_0|~m1_subset_1(X1,esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_48])).
% 8.41/8.61  cnf(c_0_54, negated_conjecture, (~r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk2_4(esk3_0,esk3_0,esk4_0,esk5_0)),esk5_0)|~r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk2_4(esk3_0,esk3_0,esk4_0,esk5_0)),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_20]), c_0_21])).
% 8.41/8.61  cnf(c_0_55, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk2_4(esk3_0,esk3_0,esk4_0,esk5_0)),esk5_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 8.41/8.61  cnf(c_0_56, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_32, c_0_52])).
% 8.41/8.61  cnf(c_0_57, negated_conjecture, (k11_relat_1(esk5_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0))=k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0))|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_27])).
% 8.41/8.61  cnf(c_0_58, negated_conjecture, (esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_46])).
% 8.41/8.61  cnf(c_0_59, negated_conjecture, (k11_relat_1(esk5_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0))=k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0))|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_56])).
% 8.41/8.61  cnf(c_0_60, negated_conjecture, (k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0))=k11_relat_1(k1_xboole_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0))|esk3_0=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58]), c_0_58]), c_0_58])).
% 8.41/8.61  cnf(c_0_61, negated_conjecture, (k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0))=k11_relat_1(k1_xboole_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0))|esk4_0=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_58]), c_0_58]), c_0_58])).
% 8.41/8.61  cnf(c_0_62, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),X1),esk4_0)|~r2_hidden(X1,k11_relat_1(k1_xboole_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_60]), c_0_43])])).
% 8.41/8.61  cnf(c_0_63, negated_conjecture, (r2_hidden(esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),k11_relat_1(k1_xboole_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)))|r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_58])).
% 8.41/8.61  cnf(c_0_64, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),X1),esk4_0)|~r2_hidden(X1,k11_relat_1(k1_xboole_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_61]), c_0_43])])).
% 8.41/8.61  cnf(c_0_65, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,esk5_0),X1),esk5_0)|~r2_hidden(X1,k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_57]), c_0_36])])).
% 8.41/8.61  cnf(c_0_66, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)),esk4_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 8.41/8.61  cnf(c_0_67, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)),esk4_0)), inference(spm,[status(thm)],[c_0_64, c_0_63])).
% 8.41/8.61  cnf(c_0_68, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),X1),k1_xboole_0)|~r2_hidden(X1,k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_58]), c_0_58]), c_0_58])).
% 8.41/8.61  cnf(c_0_69, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_66]), c_0_43])])).
% 8.41/8.61  fof(c_0_70, plain, ![X28, X29, X30, X31]:((~r2_relset_1(X28,X29,X30,X31)|X30=X31|(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))))&(X30!=X31|r2_relset_1(X28,X29,X30,X31)|(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 8.41/8.61  cnf(c_0_71, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),k11_relat_1(esk4_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_67]), c_0_43])])).
% 8.41/8.61  cnf(c_0_72, negated_conjecture, (~r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)),k1_xboole_0)|~r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_58])).
% 8.41/8.61  cnf(c_0_73, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(k4_tarski(esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 8.41/8.61  cnf(c_0_74, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 8.41/8.61  cnf(c_0_75, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk2_4(esk3_0,esk3_0,esk4_0,k1_xboole_0),k11_relat_1(k1_xboole_0,esk1_4(esk3_0,esk3_0,esk4_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_71, c_0_61])).
% 8.41/8.61  cnf(c_0_76, negated_conjecture, (esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_66])).
% 8.41/8.61  cnf(c_0_77, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_74])).
% 8.41/8.61  cnf(c_0_78, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk2_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0),k11_relat_1(k1_xboole_0,esk1_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76]), c_0_76]), c_0_76]), c_0_76])).
% 8.41/8.61  cnf(c_0_79, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_36, c_0_58])).
% 8.41/8.61  cnf(c_0_80, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_77, c_0_14])).
% 8.41/8.61  cnf(c_0_81, negated_conjecture, (~r2_relset_1(esk3_0,esk3_0,esk4_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_21, c_0_58])).
% 8.41/8.61  cnf(c_0_82, negated_conjecture, (~r2_hidden(k4_tarski(esk1_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0),esk2_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0)),k1_xboole_0)|~r2_hidden(k4_tarski(esk1_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0),esk2_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0)),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_76]), c_0_76]), c_0_76]), c_0_76]), c_0_76]), c_0_76]), c_0_76]), c_0_76])).
% 8.41/8.61  cnf(c_0_83, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(k4_tarski(esk1_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0),esk2_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_78]), c_0_79])])).
% 8.41/8.61  cnf(c_0_84, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(k4_tarski(esk1_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0),esk2_4(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0)),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_76]), c_0_76]), c_0_76]), c_0_76])).
% 8.41/8.61  cnf(c_0_85, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_58]), c_0_58])).
% 8.41/8.61  cnf(c_0_86, negated_conjecture, (~r2_relset_1(k1_xboole_0,k1_xboole_0,esk4_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_76]), c_0_76])).
% 8.41/8.61  cnf(c_0_87, negated_conjecture, (esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])).
% 8.41/8.61  cnf(c_0_88, negated_conjecture, (r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_76]), c_0_76])).
% 8.41/8.61  cnf(c_0_89, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87]), c_0_88])]), ['proof']).
% 8.41/8.61  # SZS output end CNFRefutation
% 8.41/8.61  # Proof object total steps             : 90
% 8.41/8.61  # Proof object clause steps            : 71
% 8.41/8.61  # Proof object formula steps           : 19
% 8.41/8.61  # Proof object conjectures             : 61
% 8.41/8.61  # Proof object clause conjectures      : 58
% 8.41/8.61  # Proof object formula conjectures     : 3
% 8.41/8.61  # Proof object initial clauses used    : 15
% 8.41/8.61  # Proof object initial formulas used   : 9
% 8.41/8.61  # Proof object generating inferences   : 41
% 8.41/8.61  # Proof object simplifying inferences  : 77
% 8.41/8.61  # Training examples: 0 positive, 0 negative
% 8.41/8.61  # Parsed axioms                        : 9
% 8.41/8.61  # Removed by relevancy pruning/SinE    : 0
% 8.41/8.61  # Initial clauses                      : 22
% 8.41/8.61  # Removed in clause preprocessing      : 0
% 8.41/8.61  # Initial clauses in saturation        : 22
% 8.41/8.61  # Processed clauses                    : 81400
% 8.41/8.61  # ...of these trivial                  : 9
% 8.41/8.61  # ...subsumed                          : 69490
% 8.41/8.61  # ...remaining for further processing  : 11901
% 8.41/8.61  # Other redundant clauses eliminated   : 1
% 8.41/8.61  # Clauses deleted for lack of memory   : 0
% 8.41/8.61  # Backward-subsumed                    : 139
% 8.41/8.61  # Backward-rewritten                   : 11381
% 8.41/8.61  # Generated clauses                    : 601470
% 8.41/8.61  # ...of the previous two non-trivial   : 328936
% 8.41/8.61  # Contextual simplify-reflections      : 45
% 8.41/8.61  # Paramodulations                      : 601127
% 8.41/8.61  # Factorizations                       : 342
% 8.41/8.61  # Equation resolutions                 : 1
% 8.41/8.61  # Propositional unsat checks           : 0
% 8.41/8.61  #    Propositional check models        : 0
% 8.41/8.61  #    Propositional check unsatisfiable : 0
% 8.41/8.61  #    Propositional clauses             : 0
% 8.41/8.61  #    Propositional clauses after purity: 0
% 8.41/8.61  #    Propositional unsat core size     : 0
% 8.41/8.61  #    Propositional preprocessing time  : 0.000
% 8.41/8.61  #    Propositional encoding time       : 0.000
% 8.41/8.61  #    Propositional solver time         : 0.000
% 8.41/8.61  #    Success case prop preproc time    : 0.000
% 8.41/8.61  #    Success case prop encoding time   : 0.000
% 8.41/8.61  #    Success case prop solver time     : 0.000
% 8.41/8.61  # Current number of processed clauses  : 358
% 8.41/8.61  #    Positive orientable unit clauses  : 7
% 8.41/8.61  #    Positive unorientable unit clauses: 0
% 8.41/8.61  #    Negative unit clauses             : 0
% 8.41/8.61  #    Non-unit-clauses                  : 351
% 8.41/8.61  # Current number of unprocessed clauses: 166095
% 8.41/8.61  # ...number of literals in the above   : 1614455
% 8.41/8.61  # Current number of archived formulas  : 0
% 8.41/8.61  # Current number of archived clauses   : 11542
% 8.41/8.61  # Clause-clause subsumption calls (NU) : 16917674
% 8.41/8.61  # Rec. Clause-clause subsumption calls : 1471479
% 8.41/8.61  # Non-unit clause-clause subsumptions  : 69576
% 8.41/8.61  # Unit Clause-clause subsumption calls : 1524
% 8.41/8.61  # Rewrite failures with RHS unbound    : 0
% 8.41/8.61  # BW rewrite match attempts            : 19
% 8.41/8.61  # BW rewrite match successes           : 3
% 8.41/8.61  # Condensation attempts                : 0
% 8.41/8.61  # Condensation successes               : 0
% 8.41/8.61  # Termbank termtop insertions          : 17687477
% 8.41/8.63  
% 8.41/8.63  # -------------------------------------------------
% 8.41/8.63  # User time                : 8.167 s
% 8.41/8.63  # System time              : 0.122 s
% 8.41/8.63  # Total time               : 8.289 s
% 8.41/8.63  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
