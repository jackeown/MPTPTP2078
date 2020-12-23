%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0967+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:29 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   83 (1645 expanded)
%              Number of clauses        :   61 ( 762 expanded)
%              Number of leaves         :   11 ( 430 expanded)
%              Depth                    :   20
%              Number of atoms          :  241 (5743 expanded)
%              Number of equality atoms :   72 (1456 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X2,X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t17_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X4) )
       => m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

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

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r1_tarski(X2,X3)
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_funct_2])).

fof(c_0_12,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | k1_relset_1(X14,X15,X16) = k1_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_13,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk2_0,esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & r1_tarski(esk3_0,esk4_0)
    & ( esk3_0 != k1_xboole_0
      | esk2_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(esk5_0)
      | ~ v1_funct_2(esk5_0,esk2_0,esk4_0)
      | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_14,plain,(
    ! [X26,X27,X28] :
      ( ~ r2_hidden(X26,X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X28))
      | ~ v1_xboole_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_15,plain,(
    ! [X24,X25] :
      ( ( ~ m1_subset_1(X24,k1_zfmisc_1(X25))
        | r1_tarski(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | m1_subset_1(X24,k1_zfmisc_1(X25)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_16,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | m1_subset_1(k1_relset_1(X9,X10,X11),k1_zfmisc_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_17,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X22,X23)
      | v1_xboole_0(X23)
      | r2_hidden(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_22,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_24,plain,(
    ! [X29] :
      ( ~ v1_xboole_0(X29)
      | X29 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X3)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk5_0),k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_18])])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X3,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_33,plain,(
    ! [X12] : m1_subset_1(esk1_1(X12),X12) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_34,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk5_0))
    | ~ v1_xboole_0(esk2_0)
    | ~ m1_subset_1(X1,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_38,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X17,X19)))
      | ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X19,X20)
      | m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X20))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_relset_1])])).

cnf(c_0_39,plain,
    ( X1 = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_29,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk5_0))
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_41,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_funct_2(X8,X6,X7)
        | X6 = k1_relset_1(X6,X7,X8)
        | X7 = k1_xboole_0
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( X6 != k1_relset_1(X6,X7,X8)
        | v1_funct_2(X8,X6,X7)
        | X7 = k1_xboole_0
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( ~ v1_funct_2(X8,X6,X7)
        | X6 = k1_relset_1(X6,X7,X8)
        | X6 != k1_xboole_0
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( X6 != k1_relset_1(X6,X7,X8)
        | v1_funct_2(X8,X6,X7)
        | X6 != k1_xboole_0
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( ~ v1_funct_2(X8,X6,X7)
        | X8 = k1_xboole_0
        | X6 = k1_xboole_0
        | X7 != k1_xboole_0
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
      & ( X8 != k1_xboole_0
        | v1_funct_2(X8,X6,X7)
        | X6 = k1_xboole_0
        | X7 != k1_xboole_0
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_42,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | esk3_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_34]),c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_funct_1(esk5_0)
    | ~ v1_funct_2(esk5_0,esk2_0,esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X2,X4)
    | ~ r1_tarski(X3,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( k1_relat_1(esk5_0) = o_0_0_xboole_0
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),o_0_0_xboole_0)
    | esk3_0 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_funct_2(esk5_0,esk2_0,esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(esk3_0,X2)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_18])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(o_0_0_xboole_0,esk2_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_46])).

cnf(c_0_53,plain,
    ( v1_funct_2(X1,o_0_0_xboole_0,X2)
    | k1_relset_1(o_0_0_xboole_0,X2,X1) != o_0_0_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_34]),c_0_34]),c_0_34]),c_0_34])).

cnf(c_0_54,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk5_0))
    | esk3_0 != o_0_0_xboole_0
    | ~ m1_subset_1(X1,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_48]),c_0_30])])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk2_0)
    | ~ v1_funct_2(esk5_0,esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | esk3_0 != o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_42]),c_0_30])])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(esk5_0,o_0_0_xboole_0,X1)
    | k1_relset_1(o_0_0_xboole_0,X1,esk5_0) != o_0_0_xboole_0
    | ~ r1_tarski(esk2_0,o_0_0_xboole_0)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( k1_relset_1(X1,X2,esk5_0) = k1_relat_1(esk5_0)
    | ~ r1_tarski(esk3_0,X2)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk5_0))
    | esk3_0 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_36])).

cnf(c_0_60,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_61,negated_conjecture,
    ( esk3_0 != o_0_0_xboole_0
    | ~ v1_funct_2(esk5_0,o_0_0_xboole_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_42]),c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_2(esk5_0,o_0_0_xboole_0,X1)
    | k1_relat_1(esk5_0) != o_0_0_xboole_0
    | ~ r1_tarski(esk2_0,o_0_0_xboole_0)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( k1_relat_1(esk5_0) = o_0_0_xboole_0
    | esk3_0 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_59])).

cnf(c_0_64,plain,
    ( k1_relset_1(X1,X2,X3) = X1
    | X2 = o_0_0_xboole_0
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_60,c_0_34])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_66,negated_conjecture,
    ( esk3_0 != o_0_0_xboole_0
    | ~ r1_tarski(esk2_0,o_0_0_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_51])]),c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk2_0
    | esk3_0 = o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_18]),c_0_23]),c_0_65])])).

cnf(c_0_68,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_69,negated_conjecture,
    ( esk3_0 != o_0_0_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_42]),c_0_56])).

cnf(c_0_70,negated_conjecture,
    ( esk3_0 = o_0_0_xboole_0
    | r1_tarski(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_67])).

cnf(c_0_71,plain,
    ( X1 = o_0_0_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(rw,[status(thm)],[c_0_68,c_0_34])).

cnf(c_0_72,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk2_0 ),
    inference(sr,[status(thm)],[c_0_67,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[c_0_70,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( X1 = o_0_0_xboole_0
    | v1_funct_2(esk5_0,X2,X1)
    | k1_relset_1(X2,X1,esk5_0) != X2
    | ~ r1_tarski(esk3_0,X1)
    | ~ r1_tarski(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_50])).

cnf(c_0_75,negated_conjecture,
    ( k1_relset_1(X1,X2,esk5_0) = esk2_0
    | ~ r1_tarski(esk3_0,X2)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(rw,[status(thm)],[c_0_58,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(esk4_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_51])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_funct_2(esk5_0,esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_73])])).

cnf(c_0_78,negated_conjecture,
    ( X1 = o_0_0_xboole_0
    | v1_funct_2(esk5_0,esk2_0,X1)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75])]),c_0_73])])).

cnf(c_0_79,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_36])).

cnf(c_0_80,negated_conjecture,
    ( esk4_0 = o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_51])])).

cnf(c_0_81,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80]),c_0_30])])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_81]),c_0_69]),
    [proof]).

%------------------------------------------------------------------------------
