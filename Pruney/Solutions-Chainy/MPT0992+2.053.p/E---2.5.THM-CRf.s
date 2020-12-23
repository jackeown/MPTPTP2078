%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:42 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 723 expanded)
%              Number of clauses        :   68 ( 308 expanded)
%              Number of leaves         :   16 ( 186 expanded)
%              Depth                    :   15
%              Number of atoms          :  305 (2856 expanded)
%              Number of equality atoms :   95 ( 731 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X3,X1)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(X1,X2,X4,X3))
            & v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2)
            & m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(t13_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( r1_tarski(k1_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r1_tarski(X3,X1)
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(X1,X2,X4,X3))
              & v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2)
              & m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_funct_2])).

fof(c_0_17,plain,(
    ! [X18,X19,X20] :
      ( ~ r2_hidden(X18,X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X20))
      | ~ v1_xboole_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_18,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk2_0,esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & r1_tarski(esk4_0,esk2_0)
    & ( esk3_0 != k1_xboole_0
      | esk2_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0))
      | ~ v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),esk4_0,esk3_0)
      | ~ m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_19,plain,(
    ! [X14,X15] :
      ( ( k2_zfmisc_1(X14,X15) != k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_23,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X38,X39,X40,X41] :
      ( ( v1_funct_1(k2_partfun1(X38,X39,X40,X41))
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( m1_subset_1(k2_partfun1(X38,X39,X40,X41),k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_31,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_24])).

cnf(c_0_33,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_34,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | ~ v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_funct_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0))
    | ~ v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_38,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_40,negated_conjecture,
    ( esk4_0 = esk2_0
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_32]),c_0_33])])).

fof(c_0_44,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | v1_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_35]),c_0_33])])).

cnf(c_0_47,negated_conjecture,
    ( X1 = esk5_0
    | ~ v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_21])])).

cnf(c_0_49,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_27])).

fof(c_0_52,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | r1_tarski(k7_relat_1(X22,X21),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_53,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | ~ v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_42])).

fof(c_0_58,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | ~ r1_tarski(X23,k1_relat_1(X24))
      | k1_relat_1(k7_relat_1(X24,X23)) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_59,plain,(
    ! [X42,X43,X44,X45] :
      ( ~ v1_funct_1(X44)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k2_partfun1(X42,X43,X44,X45) = k7_relat_1(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_60,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | k1_relset_1(X28,X29,X30) = k1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_61,plain,(
    ! [X35,X36,X37] :
      ( ( ~ v1_funct_2(X37,X35,X36)
        | X35 = k1_relset_1(X35,X36,X37)
        | X36 = k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X35 != k1_relset_1(X35,X36,X37)
        | v1_funct_2(X37,X35,X36)
        | X36 = k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( ~ v1_funct_2(X37,X35,X36)
        | X35 = k1_relset_1(X35,X36,X37)
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X35 != k1_relset_1(X35,X36,X37)
        | v1_funct_2(X37,X35,X36)
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( ~ v1_funct_2(X37,X35,X36)
        | X37 = k1_xboole_0
        | X35 = k1_xboole_0
        | X36 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X37 != k1_xboole_0
        | v1_funct_2(X37,X35,X36)
        | X35 = k1_xboole_0
        | X36 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_62,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,k1_xboole_0),k1_xboole_0,esk3_0)
    | ~ m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_64,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_65,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_2(esk5_0,k1_xboole_0,esk3_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_41])).

cnf(c_0_67,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_57])).

cnf(c_0_69,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_71,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_72,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v1_funct_2(k2_partfun1(esk2_0,esk3_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,esk3_0)
    | ~ m1_subset_1(k2_partfun1(esk2_0,esk3_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_74,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_64]),c_0_65])])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,esk3_0)
    | esk3_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_41])).

cnf(c_0_76,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_24]),c_0_33])])).

cnf(c_0_77,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_78,plain,(
    ! [X31,X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X31,X33)))
      | ~ r1_tarski(k1_relat_1(X34),X32)
      | m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).

cnf(c_0_79,plain,
    ( k1_relat_1(k2_partfun1(X1,X2,X3,X4)) = X4
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X4,k1_relat_1(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_53])).

cnf(c_0_80,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_70]),c_0_74]),c_0_74]),c_0_54]),c_0_54])]),c_0_75]),c_0_76])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relat_1(X2) != X3
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_71])).

cnf(c_0_83,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k1_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_84,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_85,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_70])).

cnf(c_0_86,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_55]),c_0_21])]),c_0_81])).

cnf(c_0_87,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k2_partfun1(X2,X3,X4,X5),X5,X1)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(k2_partfun1(X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X5,X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X5,k1_relat_1(X4)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_79])])).

cnf(c_0_88,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(k2_partfun1(X1,X2,X3,X4)),X5) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_90,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk5_0,X1)) = X1
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_21]),c_0_39]),c_0_86])])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_92,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_funct_2(k2_partfun1(X2,X3,esk5_0,X4),X4,X1)
    | ~ m1_subset_1(k2_partfun1(X2,X3,esk5_0,X4),k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X4,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_86]),c_0_39])])).

cnf(c_0_93,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(k1_relat_1(k2_partfun1(X1,X2,X3,X4)),k1_zfmisc_1(X5))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( k1_relat_1(k2_partfun1(X1,X2,esk5_0,X3)) = X3
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_70]),c_0_39])])).

cnf(c_0_95,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( ~ m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_92]),c_0_21]),c_0_30])]),c_0_81])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(k2_partfun1(X1,X2,esk5_0,X3),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ r1_tarski(X3,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_39])])).

cnf(c_0_98,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_21]),c_0_98]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:58:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.68/1.87  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 1.68/1.87  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.68/1.87  #
% 1.68/1.87  # Preprocessing time       : 0.028 s
% 1.68/1.87  # Presaturation interreduction done
% 1.68/1.87  
% 1.68/1.87  # Proof found!
% 1.68/1.87  # SZS status Theorem
% 1.68/1.87  # SZS output start CNFRefutation
% 1.68/1.87  fof(t38_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 1.68/1.87  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 1.68/1.87  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.68/1.87  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.68/1.87  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.68/1.87  fof(dt_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_funct_1(k2_partfun1(X1,X2,X3,X4))&m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 1.68/1.87  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.68/1.87  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.68/1.87  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.68/1.87  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.68/1.87  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 1.68/1.87  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 1.68/1.87  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 1.68/1.87  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.68/1.87  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 1.68/1.87  fof(t13_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>(r1_tarski(k1_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 1.68/1.87  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))))))), inference(assume_negation,[status(cth)],[t38_funct_2])).
% 1.68/1.87  fof(c_0_17, plain, ![X18, X19, X20]:(~r2_hidden(X18,X19)|~m1_subset_1(X19,k1_zfmisc_1(X20))|~v1_xboole_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 1.68/1.87  fof(c_0_18, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(r1_tarski(esk4_0,esk2_0)&((esk3_0!=k1_xboole_0|esk2_0=k1_xboole_0)&(~v1_funct_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0))|~v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),esk4_0,esk3_0)|~m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 1.68/1.87  fof(c_0_19, plain, ![X14, X15]:((k2_zfmisc_1(X14,X15)!=k1_xboole_0|(X14=k1_xboole_0|X15=k1_xboole_0))&((X14!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0)&(X15!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 1.68/1.87  cnf(c_0_20, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.68/1.87  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.68/1.87  fof(c_0_22, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.68/1.87  fof(c_0_23, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.68/1.87  cnf(c_0_24, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.68/1.87  cnf(c_0_25, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.68/1.87  cnf(c_0_26, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 1.68/1.87  cnf(c_0_27, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.68/1.87  fof(c_0_28, plain, ![X38, X39, X40, X41]:((v1_funct_1(k2_partfun1(X38,X39,X40,X41))|(~v1_funct_1(X40)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))&(m1_subset_1(k2_partfun1(X38,X39,X40,X41),k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|(~v1_funct_1(X40)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).
% 1.68/1.87  cnf(c_0_29, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.68/1.87  cnf(c_0_30, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.68/1.87  fof(c_0_31, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 1.68/1.87  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_24])).
% 1.68/1.87  cnf(c_0_33, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 1.68/1.87  fof(c_0_34, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.68/1.87  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_25])).
% 1.68/1.87  cnf(c_0_36, negated_conjecture, (r1_tarski(esk5_0,X1)|~v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 1.68/1.87  cnf(c_0_37, negated_conjecture, (~v1_funct_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0))|~v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),esk4_0,esk3_0)|~m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.68/1.87  cnf(c_0_38, plain, (v1_funct_1(k2_partfun1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.68/1.87  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.68/1.87  cnf(c_0_40, negated_conjecture, (esk4_0=esk2_0|~r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.68/1.87  cnf(c_0_41, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.68/1.87  cnf(c_0_42, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.68/1.87  cnf(c_0_43, negated_conjecture, (esk3_0!=k1_xboole_0|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_32]), c_0_33])])).
% 1.68/1.87  fof(c_0_44, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|v1_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 1.68/1.87  cnf(c_0_45, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.68/1.87  cnf(c_0_46, negated_conjecture, (esk2_0!=k1_xboole_0|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_35]), c_0_33])])).
% 1.68/1.87  cnf(c_0_47, negated_conjecture, (X1=esk5_0|~v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_29, c_0_36])).
% 1.68/1.87  cnf(c_0_48, negated_conjecture, (~v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),esk4_0,esk3_0)|~m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_21])])).
% 1.68/1.87  cnf(c_0_49, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 1.68/1.87  cnf(c_0_50, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_42])).
% 1.68/1.87  cnf(c_0_51, negated_conjecture, (r1_tarski(esk5_0,X1)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_27])).
% 1.68/1.87  fof(c_0_52, plain, ![X21, X22]:(~v1_relat_1(X22)|r1_tarski(k7_relat_1(X22,X21),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 1.68/1.87  cnf(c_0_53, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.68/1.87  cnf(c_0_54, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_45, c_0_42])).
% 1.68/1.87  cnf(c_0_55, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.68/1.87  cnf(c_0_56, negated_conjecture, (r1_tarski(esk5_0,X1)|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_27])).
% 1.68/1.87  cnf(c_0_57, negated_conjecture, (esk5_0=k1_xboole_0|~v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_47, c_0_42])).
% 1.68/1.87  fof(c_0_58, plain, ![X23, X24]:(~v1_relat_1(X24)|(~r1_tarski(X23,k1_relat_1(X24))|k1_relat_1(k7_relat_1(X24,X23))=X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 1.68/1.87  fof(c_0_59, plain, ![X42, X43, X44, X45]:(~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|k2_partfun1(X42,X43,X44,X45)=k7_relat_1(X44,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 1.68/1.87  fof(c_0_60, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|k1_relset_1(X28,X29,X30)=k1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 1.68/1.87  fof(c_0_61, plain, ![X35, X36, X37]:((((~v1_funct_2(X37,X35,X36)|X35=k1_relset_1(X35,X36,X37)|X36=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(X35!=k1_relset_1(X35,X36,X37)|v1_funct_2(X37,X35,X36)|X36=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))&((~v1_funct_2(X37,X35,X36)|X35=k1_relset_1(X35,X36,X37)|X35!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(X35!=k1_relset_1(X35,X36,X37)|v1_funct_2(X37,X35,X36)|X35!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))))&((~v1_funct_2(X37,X35,X36)|X37=k1_xboole_0|X35=k1_xboole_0|X36!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(X37!=k1_xboole_0|v1_funct_2(X37,X35,X36)|X35=k1_xboole_0|X36!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 1.68/1.87  cnf(c_0_62, negated_conjecture, (esk3_0!=k1_xboole_0|~v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,k1_xboole_0),k1_xboole_0,esk3_0)|~m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk3_0)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.68/1.87  cnf(c_0_63, negated_conjecture, (esk5_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.68/1.87  cnf(c_0_64, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.68/1.87  cnf(c_0_65, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 1.68/1.87  cnf(c_0_66, negated_conjecture, (v1_funct_2(esk5_0,k1_xboole_0,esk3_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_41])).
% 1.68/1.87  cnf(c_0_67, negated_conjecture, (esk5_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_56])).
% 1.68/1.87  cnf(c_0_68, negated_conjecture, (v1_funct_1(k1_xboole_0)|~v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_39, c_0_57])).
% 1.68/1.87  cnf(c_0_69, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.68/1.87  cnf(c_0_70, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 1.68/1.87  cnf(c_0_71, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 1.68/1.87  cnf(c_0_72, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.68/1.87  cnf(c_0_73, negated_conjecture, (esk3_0!=k1_xboole_0|~v1_funct_2(k2_partfun1(esk2_0,esk3_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,esk3_0)|~m1_subset_1(k2_partfun1(esk2_0,esk3_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk3_0)))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 1.68/1.87  cnf(c_0_74, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_64]), c_0_65])])).
% 1.68/1.87  cnf(c_0_75, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,esk3_0)|esk3_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_41])).
% 1.68/1.87  cnf(c_0_76, negated_conjecture, (v1_funct_1(k1_xboole_0)|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_24]), c_0_33])])).
% 1.68/1.87  cnf(c_0_77, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.68/1.87  fof(c_0_78, plain, ![X31, X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X31,X33)))|(~r1_tarski(k1_relat_1(X34),X32)|m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).
% 1.68/1.87  cnf(c_0_79, plain, (k1_relat_1(k2_partfun1(X1,X2,X3,X4))=X4|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(X4,k1_relat_1(X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_53])).
% 1.68/1.87  cnf(c_0_80, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 1.68/1.87  cnf(c_0_81, negated_conjecture, (esk3_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_70]), c_0_74]), c_0_74]), c_0_54]), c_0_54])]), c_0_75]), c_0_76])).
% 1.68/1.87  cnf(c_0_82, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relat_1(X2)!=X3|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(spm,[status(thm)],[c_0_77, c_0_71])).
% 1.68/1.87  cnf(c_0_83, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k1_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 1.68/1.87  cnf(c_0_84, plain, (m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.68/1.87  cnf(c_0_85, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~r1_tarski(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_79, c_0_70])).
% 1.68/1.87  cnf(c_0_86, negated_conjecture, (k1_relat_1(esk5_0)=esk2_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_55]), c_0_21])]), c_0_81])).
% 1.68/1.87  cnf(c_0_87, plain, (X1=k1_xboole_0|v1_funct_2(k2_partfun1(X2,X3,X4,X5),X5,X1)|~v1_funct_1(X4)|~m1_subset_1(k2_partfun1(X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X5,X1)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(X5,k1_relat_1(X4))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_79])])).
% 1.68/1.87  cnf(c_0_88, plain, (m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(k1_relat_1(k2_partfun1(X1,X2,X3,X4)),X5)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 1.68/1.87  cnf(c_0_89, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.68/1.87  cnf(c_0_90, negated_conjecture, (k1_relat_1(k7_relat_1(esk5_0,X1))=X1|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_21]), c_0_39]), c_0_86])])).
% 1.68/1.87  cnf(c_0_91, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.68/1.87  cnf(c_0_92, negated_conjecture, (X1=k1_xboole_0|v1_funct_2(k2_partfun1(X2,X3,esk5_0,X4),X4,X1)|~m1_subset_1(k2_partfun1(X2,X3,esk5_0,X4),k1_zfmisc_1(k2_zfmisc_1(X4,X1)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(X4,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_86]), c_0_39])])).
% 1.68/1.87  cnf(c_0_93, plain, (m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X5,X2)))|~v1_funct_1(X3)|~m1_subset_1(k1_relat_1(k2_partfun1(X1,X2,X3,X4)),k1_zfmisc_1(X5))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 1.68/1.87  cnf(c_0_94, negated_conjecture, (k1_relat_1(k2_partfun1(X1,X2,esk5_0,X3))=X3|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(X3,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_70]), c_0_39])])).
% 1.68/1.87  cnf(c_0_95, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_91])).
% 1.68/1.87  cnf(c_0_96, negated_conjecture, (~m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_92]), c_0_21]), c_0_30])]), c_0_81])).
% 1.68/1.87  cnf(c_0_97, negated_conjecture, (m1_subset_1(k2_partfun1(X1,X2,esk5_0,X3),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~r1_tarski(X3,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_39])])).
% 1.68/1.87  cnf(c_0_98, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_45, c_0_95])).
% 1.68/1.87  cnf(c_0_99, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_21]), c_0_98]), c_0_30])]), ['proof']).
% 1.68/1.87  # SZS output end CNFRefutation
% 1.68/1.87  # Proof object total steps             : 100
% 1.68/1.87  # Proof object clause steps            : 68
% 1.68/1.87  # Proof object formula steps           : 32
% 1.68/1.87  # Proof object conjectures             : 38
% 1.68/1.87  # Proof object clause conjectures      : 35
% 1.68/1.87  # Proof object formula conjectures     : 3
% 1.68/1.87  # Proof object initial clauses used    : 26
% 1.68/1.87  # Proof object initial formulas used   : 16
% 1.68/1.87  # Proof object generating inferences   : 41
% 1.68/1.87  # Proof object simplifying inferences  : 44
% 1.68/1.87  # Training examples: 0 positive, 0 negative
% 1.68/1.87  # Parsed axioms                        : 16
% 1.68/1.87  # Removed by relevancy pruning/SinE    : 0
% 1.68/1.87  # Initial clauses                      : 34
% 1.68/1.87  # Removed in clause preprocessing      : 0
% 1.68/1.87  # Initial clauses in saturation        : 34
% 1.68/1.87  # Processed clauses                    : 37637
% 1.68/1.87  # ...of these trivial                  : 106
% 1.68/1.87  # ...subsumed                          : 34921
% 1.68/1.87  # ...remaining for further processing  : 2610
% 1.68/1.87  # Other redundant clauses eliminated   : 304
% 1.68/1.87  # Clauses deleted for lack of memory   : 0
% 1.68/1.87  # Backward-subsumed                    : 491
% 1.68/1.87  # Backward-rewritten                   : 164
% 1.68/1.87  # Generated clauses                    : 130738
% 1.68/1.87  # ...of the previous two non-trivial   : 120191
% 1.68/1.87  # Contextual simplify-reflections      : 474
% 1.68/1.87  # Paramodulations                      : 130192
% 1.68/1.87  # Factorizations                       : 2
% 1.68/1.87  # Equation resolutions                 : 544
% 1.68/1.87  # Propositional unsat checks           : 0
% 1.68/1.87  #    Propositional check models        : 0
% 1.68/1.87  #    Propositional check unsatisfiable : 0
% 1.68/1.87  #    Propositional clauses             : 0
% 1.68/1.87  #    Propositional clauses after purity: 0
% 1.68/1.87  #    Propositional unsat core size     : 0
% 1.68/1.87  #    Propositional preprocessing time  : 0.000
% 1.68/1.87  #    Propositional encoding time       : 0.000
% 1.68/1.87  #    Propositional solver time         : 0.000
% 1.68/1.87  #    Success case prop preproc time    : 0.000
% 1.68/1.87  #    Success case prop encoding time   : 0.000
% 1.68/1.87  #    Success case prop solver time     : 0.000
% 1.68/1.87  # Current number of processed clauses  : 1920
% 1.68/1.87  #    Positive orientable unit clauses  : 46
% 1.68/1.87  #    Positive unorientable unit clauses: 0
% 1.68/1.87  #    Negative unit clauses             : 19
% 1.68/1.87  #    Non-unit-clauses                  : 1855
% 1.68/1.87  # Current number of unprocessed clauses: 78713
% 1.68/1.87  # ...number of literals in the above   : 413504
% 1.68/1.87  # Current number of archived formulas  : 0
% 1.68/1.87  # Current number of archived clauses   : 688
% 1.68/1.87  # Clause-clause subsumption calls (NU) : 828422
% 1.68/1.87  # Rec. Clause-clause subsumption calls : 221566
% 1.68/1.87  # Non-unit clause-clause subsumptions  : 12577
% 1.68/1.87  # Unit Clause-clause subsumption calls : 2914
% 1.68/1.87  # Rewrite failures with RHS unbound    : 20
% 1.68/1.87  # BW rewrite match attempts            : 544
% 1.68/1.87  # BW rewrite match successes           : 40
% 1.68/1.87  # Condensation attempts                : 0
% 1.68/1.87  # Condensation successes               : 0
% 1.68/1.87  # Termbank termtop insertions          : 2096617
% 1.68/1.87  
% 1.68/1.87  # -------------------------------------------------
% 1.68/1.87  # User time                : 1.502 s
% 1.68/1.87  # System time              : 0.038 s
% 1.68/1.87  # Total time               : 1.539 s
% 1.68/1.87  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
