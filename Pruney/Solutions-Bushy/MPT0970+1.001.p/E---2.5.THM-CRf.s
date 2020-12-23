%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0970+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:29 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 442 expanded)
%              Number of clauses        :   50 ( 191 expanded)
%              Number of leaves         :   14 ( 109 expanded)
%              Depth                    :   15
%              Number of atoms          :  259 (1782 expanded)
%              Number of equality atoms :   81 ( 503 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] :
                  ~ ( r2_hidden(X5,X1)
                    & X4 = k1_funct_1(X3,X5) ) )
       => k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ! [X4] :
              ~ ( r2_hidden(X4,X2)
                & ! [X5] :
                    ~ ( r2_hidden(X5,X1)
                      & X4 = k1_funct_1(X3,X5) ) )
         => k2_relset_1(X1,X2,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t16_funct_2])).

fof(c_0_15,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k2_relset_1(X33,X34,X35) = k2_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_16,negated_conjecture,(
    ! [X52] :
      ( v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,esk5_0,esk6_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & ( r2_hidden(esk8_1(X52),esk5_0)
        | ~ r2_hidden(X52,esk6_0) )
      & ( X52 = k1_funct_1(esk7_0,esk8_1(X52))
        | ~ r2_hidden(X52,esk6_0) )
      & k2_relset_1(esk5_0,esk6_0,esk7_0) != esk6_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])])).

fof(c_0_17,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_relat_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_18,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | m1_subset_1(k2_relset_1(X25,X26,X27),k1_zfmisc_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_19,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X15,X16,X17,X19,X20,X21,X23] :
      ( ( r2_hidden(esk1_3(X15,X16,X17),k1_relat_1(X15))
        | ~ r2_hidden(X17,X16)
        | X16 != k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( X17 = k1_funct_1(X15,esk1_3(X15,X16,X17))
        | ~ r2_hidden(X17,X16)
        | X16 != k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(X20,k1_relat_1(X15))
        | X19 != k1_funct_1(X15,X20)
        | r2_hidden(X19,X16)
        | X16 != k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(esk2_2(X15,X21),X21)
        | ~ r2_hidden(X23,k1_relat_1(X15))
        | esk2_2(X15,X21) != k1_funct_1(X15,X23)
        | X21 = k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(esk3_2(X15,X21),k1_relat_1(X15))
        | r2_hidden(esk2_2(X15,X21),X21)
        | X21 = k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( esk2_2(X15,X21) = k1_funct_1(X15,esk3_2(X15,X21))
        | r2_hidden(esk2_2(X15,X21),X21)
        | X21 = k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_22,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X43,X44,X45] :
      ( ~ r2_hidden(X43,X44)
      | ~ m1_subset_1(X44,k1_zfmisc_1(X45))
      | ~ v1_xboole_0(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_24,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k2_relset_1(esk5_0,esk6_0,esk7_0) = k2_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_26,plain,(
    ! [X40,X41,X42] :
      ( ~ r2_hidden(X40,X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(X42))
      | m1_subset_1(X40,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( esk2_2(X1,X2) = k1_funct_1(X1,esk3_2(X1,X2))
    | r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_31,plain,
    ( r2_hidden(esk3_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_32,plain,(
    ! [X46] :
      ( ~ v1_xboole_0(X46)
      | X46 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_20])])).

fof(c_0_35,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X38,X39)
      | v1_xboole_0(X39)
      | r2_hidden(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_27])])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_2(esk7_0,X1)) = esk2_2(esk7_0,X1)
    | X1 = k2_relat_1(esk7_0)
    | r2_hidden(esk2_2(esk7_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_39,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | r2_hidden(esk3_2(esk7_0,X1),k1_relat_1(esk7_0))
    | r2_hidden(esk2_2(esk7_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_30])])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk7_0))
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_44,plain,(
    ! [X28] : m1_subset_1(esk4_1(X28),X28) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_45,plain,(
    ! [X36,X37] :
      ( ~ r2_hidden(X36,X37)
      | m1_subset_1(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | r2_hidden(esk2_2(esk7_0,X1),k2_relat_1(esk7_0))
    | r2_hidden(esk2_2(esk7_0,X1),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_29]),c_0_30])]),c_0_39])).

cnf(c_0_48,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk7_0))
    | ~ v1_xboole_0(esk6_0)
    | ~ m1_subset_1(X1,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( m1_subset_1(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | r2_hidden(esk2_2(esk7_0,X1),X1)
    | m1_subset_1(esk2_2(esk7_0,X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( k2_relset_1(esk5_0,esk6_0,esk7_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_54,plain,
    ( X1 = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_40,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk7_0))
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_56,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v1_funct_2(X14,X12,X13)
        | X12 = k1_relset_1(X12,X13,X14)
        | X13 = k1_xboole_0
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) )
      & ( X12 != k1_relset_1(X12,X13,X14)
        | v1_funct_2(X14,X12,X13)
        | X13 = k1_xboole_0
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) )
      & ( ~ v1_funct_2(X14,X12,X13)
        | X12 = k1_relset_1(X12,X13,X14)
        | X12 != k1_xboole_0
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) )
      & ( X12 != k1_relset_1(X12,X13,X14)
        | v1_funct_2(X14,X12,X13)
        | X12 != k1_xboole_0
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) )
      & ( ~ v1_funct_2(X14,X12,X13)
        | X14 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 != k1_xboole_0
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) )
      & ( X14 != k1_xboole_0
        | v1_funct_2(X14,X12,X13)
        | X12 = k1_xboole_0
        | X13 != k1_xboole_0
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_57,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k1_relset_1(X30,X31,X32) = k1_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_58,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | esk2_2(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_59,negated_conjecture,
    ( X1 = k2_relat_1(esk7_0)
    | m1_subset_1(esk2_2(esk7_0,X1),esk6_0)
    | m1_subset_1(esk2_2(esk7_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( k2_relat_1(esk7_0) != esk6_0 ),
    inference(rw,[status(thm)],[c_0_53,c_0_25])).

cnf(c_0_61,negated_conjecture,
    ( k2_relat_1(esk7_0) = o_0_0_xboole_0
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,plain,
    ( X1 = k2_relat_1(X2)
    | v1_xboole_0(X1)
    | esk2_2(X2,X1) != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ m1_subset_1(esk2_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_43])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk2_2(esk7_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_59]),c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_54])).

cnf(c_0_67,plain,
    ( k1_relset_1(X1,X2,X3) = X1
    | X2 = o_0_0_xboole_0
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_62,c_0_48])).

cnf(c_0_68,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk7_0) = k1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_20])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_70,negated_conjecture,
    ( esk2_2(esk7_0,esk6_0) != k1_funct_1(esk7_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_29]),c_0_30])]),c_0_60]),c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0
    | esk6_0 = o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_20]),c_0_68]),c_0_69])])).

cnf(c_0_72,negated_conjecture,
    ( esk6_0 = o_0_0_xboole_0
    | esk2_2(esk7_0,esk6_0) != k1_funct_1(esk7_0,X1)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_73,negated_conjecture,
    ( X1 = k1_funct_1(esk7_0,esk8_1(X1))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk8_1(X1),esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_75,negated_conjecture,
    ( esk6_0 = o_0_0_xboole_0
    | ~ r2_hidden(esk2_2(esk7_0,esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73])]),c_0_74])).

cnf(c_0_76,negated_conjecture,
    ( esk6_0 = o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_43]),c_0_65])]),c_0_66])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_76]),c_0_41])]),
    [proof]).

%------------------------------------------------------------------------------
