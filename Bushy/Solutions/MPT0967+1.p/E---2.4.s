%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t9_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:53 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  120 (5859 expanded)
%              Number of clauses        :   94 (2756 expanded)
%              Number of leaves         :   13 (1542 expanded)
%              Depth                    :   21
%              Number of atoms          :  326 (19682 expanded)
%              Number of equality atoms :   86 (4819 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',t9_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',redefinition_k1_relset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',t5_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',t3_subset)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',dt_k1_relset_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',existence_m1_subset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',t8_boole)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',cc4_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',t2_subset)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',dt_o_0_0_xboole_0)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',t6_boole)).

fof(t17_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X4) )
       => m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',t17_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',d1_funct_2)).

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k1_relset_1(X20,X21,X22) = k1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_15,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r1_tarski(esk2_0,esk3_0)
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(esk4_0)
      | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
      | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_16,plain,(
    ! [X37,X38,X39] :
      ( ~ r2_hidden(X37,X38)
      | ~ m1_subset_1(X38,k1_zfmisc_1(X39))
      | ~ v1_xboole_0(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_17,plain,(
    ! [X32,X33] :
      ( ( ~ m1_subset_1(X32,k1_zfmisc_1(X33))
        | r1_tarski(X32,X33) )
      & ( ~ r1_tarski(X32,X33)
        | m1_subset_1(X32,k1_zfmisc_1(X33)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_18,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | m1_subset_1(k1_relset_1(X15,X16,X17),k1_zfmisc_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_19,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X18] : m1_subset_1(esk5_1(X18),X18) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_22,plain,(
    ! [X43,X44] :
      ( ~ v1_xboole_0(X43)
      | X43 = X44
      | ~ v1_xboole_0(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_23,plain,(
    ! [X45,X46,X47] :
      ( ~ v1_xboole_0(X45)
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X45)))
      | v1_xboole_0(X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X30,X31)
      | v1_xboole_0(X31)
      | r2_hidden(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_27,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X40] :
      ( ~ v1_xboole_0(X40)
      | X40 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_34,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_20])])).

cnf(c_0_38,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_relset_1(X1,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_27])).

cnf(c_0_39,plain,
    ( k1_relset_1(X1,X2,esk5_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k1_relat_1(esk5_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_29])).

cnf(c_0_40,plain,
    ( X1 = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,plain,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

fof(c_0_42,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X23,X25)))
      | ~ r1_tarski(X23,X24)
      | ~ r1_tarski(X25,X26)
      | m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_relset_1])])).

fof(c_0_43,plain,(
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

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_relat_1(esk5_1(k1_zfmisc_1(k2_zfmisc_1(X1,X3))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_29])])).

cnf(c_0_48,plain,
    ( esk5_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = o_0_0_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X2,X4)
    | ~ r1_tarski(X3,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_31])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk4_0))
    | ~ v1_xboole_0(esk1_0)
    | ~ m1_subset_1(X1,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,k1_relat_1(o_0_0_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(esk2_0,X2)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_20])).

cnf(c_0_55,plain,
    ( k1_relset_1(X1,X2,X3) = X1
    | X2 = o_0_0_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X3,X1,X2) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk4_0))
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_29])).

cnf(c_0_58,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_59,plain,
    ( v1_xboole_0(k1_relat_1(o_0_0_xboole_0))
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X3,k1_relat_1(o_0_0_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_35])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(X1)
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(esk1_0,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_62,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0
    | esk2_0 = o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_20]),c_0_28]),c_0_56])])).

cnf(c_0_63,negated_conjecture,
    ( k1_relat_1(esk4_0) = o_0_0_xboole_0
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( esk1_0 = o_0_0_xboole_0
    | esk2_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_51]),c_0_51])).

cnf(c_0_65,plain,
    ( v1_xboole_0(k1_relat_1(o_0_0_xboole_0))
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_29])).

cnf(c_0_66,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(esk3_0)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | r1_tarski(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_70,negated_conjecture,
    ( k1_relat_1(esk4_0) = o_0_0_xboole_0
    | esk2_0 != o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_31])])).

cnf(c_0_71,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_72,plain,
    ( v1_xboole_0(k1_relat_1(o_0_0_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_31])).

cnf(c_0_73,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(o_0_0_xboole_0,esk1_0)
    | esk2_0 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_70])).

cnf(c_0_76,plain,
    ( v1_funct_2(X1,o_0_0_xboole_0,X2)
    | k1_relset_1(o_0_0_xboole_0,X2,X1) != o_0_0_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_71]),c_0_51]),c_0_51]),c_0_51]),c_0_51])).

cnf(c_0_77,plain,
    ( r1_tarski(k1_relset_1(X1,X2,X3),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_27])).

cnf(c_0_78,plain,
    ( v1_xboole_0(k1_relat_1(o_0_0_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_31])).

cnf(c_0_79,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(esk3_0)
    | ~ r1_tarski(o_0_0_xboole_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_64]),c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk1_0)
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_54]),c_0_61])])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | esk2_0 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_64])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_2(esk4_0,o_0_0_xboole_0,X1)
    | k1_relset_1(o_0_0_xboole_0,X1,esk4_0) != o_0_0_xboole_0
    | ~ r1_tarski(esk1_0,o_0_0_xboole_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_54])).

cnf(c_0_83,negated_conjecture,
    ( k1_relset_1(X1,X2,esk4_0) = k1_relat_1(esk4_0)
    | ~ r1_tarski(esk2_0,X2)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_54])).

cnf(c_0_84,plain,
    ( r1_tarski(k1_relat_1(esk5_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_29]),c_0_39])).

cnf(c_0_85,plain,
    ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_78])).

cnf(c_0_86,plain,
    ( X1 = esk5_1(k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_41])).

cnf(c_0_87,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_75]),c_0_73])).

cnf(c_0_88,negated_conjecture,
    ( esk2_0 != o_0_0_xboole_0
    | ~ v1_funct_2(esk4_0,o_0_0_xboole_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_64]),c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( v1_funct_2(esk4_0,o_0_0_xboole_0,X1)
    | k1_relat_1(esk4_0) != o_0_0_xboole_0
    | ~ r1_tarski(esk1_0,o_0_0_xboole_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_90,plain,
    ( r1_tarski(o_0_0_xboole_0,X1)
    | ~ v1_xboole_0(X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_48]),c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( esk5_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = esk4_0
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( esk2_0 != o_0_0_xboole_0
    | ~ r1_tarski(esk1_0,o_0_0_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_61])]),c_0_70])).

cnf(c_0_93,plain,
    ( r1_tarski(o_0_0_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_31])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),X1)
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_91])).

cnf(c_0_95,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_96,negated_conjecture,
    ( esk2_0 != o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_64]),c_0_93])])).

cnf(c_0_97,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_25])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),X1)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_87])).

cnf(c_0_99,plain,
    ( X1 = o_0_0_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(rw,[status(thm)],[c_0_95,c_0_51])).

cnf(c_0_100,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0 ),
    inference(sr,[status(thm)],[c_0_62,c_0_96])).

cnf(c_0_101,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk4_0))
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_25])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[c_0_67,c_0_96])).

cnf(c_0_104,negated_conjecture,
    ( X1 = o_0_0_xboole_0
    | v1_funct_2(esk4_0,X2,X1)
    | k1_relset_1(X2,X1,esk4_0) != X2
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(esk1_0,X2) ),
    inference(spm,[status(thm)],[c_0_99,c_0_54])).

cnf(c_0_105,negated_conjecture,
    ( k1_relset_1(X1,X2,esk4_0) = esk1_0
    | ~ r1_tarski(esk2_0,X2)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(rw,[status(thm)],[c_0_83,c_0_100])).

cnf(c_0_106,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk4_0))
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_87])).

cnf(c_0_107,plain,
    ( k1_relset_1(X1,X2,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_93]),c_0_85])).

cnf(c_0_108,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_103])])).

cnf(c_0_109,negated_conjecture,
    ( X1 = o_0_0_xboole_0
    | v1_funct_2(esk4_0,esk1_0,X1)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105])]),c_0_103])])).

cnf(c_0_110,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | v1_xboole_0(esk1_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_62])).

cnf(c_0_111,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_107])).

cnf(c_0_112,negated_conjecture,
    ( esk4_0 = o_0_0_xboole_0
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_87])).

cnf(c_0_113,negated_conjecture,
    ( esk3_0 = o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_61])])).

cnf(c_0_114,negated_conjecture,
    ( esk1_0 = o_0_0_xboole_0
    | ~ v1_xboole_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_110]),c_0_64])).

cnf(c_0_115,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_25]),c_0_93])])).

cnf(c_0_116,negated_conjecture,
    ( esk4_0 = o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_113]),c_0_31])])).

cnf(c_0_117,negated_conjecture,
    ( esk1_0 = o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_113]),c_0_31])])).

cnf(c_0_118,plain,
    ( v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_115]),c_0_107])])).

cnf(c_0_119,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_113]),c_0_116]),c_0_117]),c_0_118])]),
    [proof]).
%------------------------------------------------------------------------------
