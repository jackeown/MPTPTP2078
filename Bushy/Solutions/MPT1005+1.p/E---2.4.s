%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t59_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:47 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   48 (  67 expanded)
%              Number of clauses        :   26 (  30 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  143 ( 201 expanded)
%              Number of equality atoms :   32 (  47 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t59_funct_2.p',t5_subset)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t59_funct_2.p',dt_k1_relset_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t59_funct_2.p',t6_boole)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t59_funct_2.p',redefinition_k1_relset_1)).

fof(t59_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_xboole_0,X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
     => k7_relset_1(k1_xboole_0,X1,X3,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t59_funct_2.p',t59_funct_2)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t59_funct_2.p',dt_o_0_0_xboole_0)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t59_funct_2.p',cc1_relset_1)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t59_funct_2.p',d12_funct_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t59_funct_2.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t59_funct_2.p',existence_m1_subset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t59_funct_2.p',redefinition_k7_relset_1)).

fof(c_0_11,plain,(
    ! [X51,X52,X53] :
      ( ~ r2_hidden(X51,X52)
      | ~ m1_subset_1(X52,k1_zfmisc_1(X53))
      | ~ v1_xboole_0(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_12,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | m1_subset_1(k1_relset_1(X23,X24,X25),k1_zfmisc_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

fof(c_0_13,plain,(
    ! [X54] :
      ( ~ v1_xboole_0(X54)
      | X54 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k1_relset_1(X35,X36,X37) = k1_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_xboole_0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
       => k7_relset_1(k1_xboole_0,X1,X3,X2) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t59_funct_2])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_20,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_relset_1(X1,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,k1_xboole_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk1_0)))
    & k7_relset_1(k1_xboole_0,esk1_0,esk3_0,esk2_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_23,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,plain,(
    ! [X59,X60,X61] :
      ( ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
      | v1_relat_1(X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_25,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_relat_1(X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_23])).

fof(c_0_28,plain,(
    ! [X11,X12,X13,X14,X16,X17,X18,X19,X21] :
      ( ( r2_hidden(esk4_4(X11,X12,X13,X14),k1_relat_1(X11))
        | ~ r2_hidden(X14,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk4_4(X11,X12,X13,X14),X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( X14 = k1_funct_1(X11,esk4_4(X11,X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(X17,k1_relat_1(X11))
        | ~ r2_hidden(X17,X12)
        | X16 != k1_funct_1(X11,X17)
        | r2_hidden(X16,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(esk5_3(X11,X18,X19),X19)
        | ~ r2_hidden(X21,k1_relat_1(X11))
        | ~ r2_hidden(X21,X18)
        | esk5_3(X11,X18,X19) != k1_funct_1(X11,X21)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk6_3(X11,X18,X19),k1_relat_1(X11))
        | r2_hidden(esk5_3(X11,X18,X19),X19)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk6_3(X11,X18,X19),X18)
        | r2_hidden(esk5_3(X11,X18,X19),X19)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk5_3(X11,X18,X19) = k1_funct_1(X11,esk6_3(X11,X18,X19))
        | r2_hidden(esk5_3(X11,X18,X19),X19)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

cnf(c_0_29,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_31,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_34,plain,(
    ! [X44,X45] :
      ( ~ m1_subset_1(X44,X45)
      | v1_xboole_0(X45)
      | r2_hidden(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_35,plain,(
    ! [X33] : m1_subset_1(esk7_1(X33),X33) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_36,negated_conjecture,
    ( X1 != k9_relat_1(esk3_0,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk7_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_39,plain,(
    ! [X38,X39,X40,X41] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | k7_relset_1(X38,X39,X40,X41) = k9_relat_1(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(X1,k9_relat_1(esk3_0,X2)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk7_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( k7_relset_1(k1_xboole_0,esk1_0,esk3_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_43,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( v1_xboole_0(k9_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( k9_relat_1(esk3_0,esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_26])])).

cnf(c_0_46,negated_conjecture,
    ( k9_relat_1(esk3_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
