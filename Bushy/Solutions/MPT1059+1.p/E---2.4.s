%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t176_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:37 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 193 expanded)
%              Number of clauses        :   45 (  78 expanded)
%              Number of leaves         :   13 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :  208 ( 767 expanded)
%              Number of equality atoms :   54 ( 131 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t176_funct_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => k7_partfun1(X2,X3,X4) = k3_funct_2(X1,X2,X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t176_funct_2.p',t176_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t176_funct_2.p',redefinition_k1_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t176_funct_2.p',cc1_relset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t176_funct_2.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t176_funct_2.p',existence_m1_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t176_funct_2.p',t2_subset)).

fof(dt_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => m1_subset_1(k3_funct_2(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t176_funct_2.p',dt_k3_funct_2)).

fof(d8_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => k7_partfun1(X1,X2,X3) = k1_funct_1(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t176_funct_2.p',d8_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t176_funct_2.p',d1_funct_2)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t176_funct_2.p',redefinition_k3_funct_2)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t176_funct_2.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t176_funct_2.p',dt_o_0_0_xboole_0)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t176_funct_2.p',cc2_relset_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
               => ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => k7_partfun1(X2,X3,X4) = k3_funct_2(X1,X2,X3,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t176_funct_2])).

fof(c_0_14,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k1_relset_1(X29,X30,X31) = k1_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_15,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & m1_subset_1(esk4_0,esk1_0)
    & k7_partfun1(esk2_0,esk3_0,esk4_0) != k3_funct_2(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X53,X54,X55] :
      ( ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
      | v1_relat_1(X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_17,plain,(
    ! [X45,X46,X47] :
      ( ~ r2_hidden(X45,X46)
      | ~ m1_subset_1(X46,k1_zfmisc_1(X47))
      | ~ v1_xboole_0(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_18,plain,(
    ! [X27] : m1_subset_1(esk5_1(X27),X27) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_19,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X38,X39)
      | v1_xboole_0(X39)
      | r2_hidden(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_20,plain,(
    ! [X20,X21,X22,X23] :
      ( v1_xboole_0(X20)
      | ~ v1_funct_1(X22)
      | ~ v1_funct_2(X22,X20,X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | ~ m1_subset_1(X23,X20)
      | m1_subset_1(k3_funct_2(X20,X21,X22,X23),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_funct_2])])])).

fof(c_0_21,plain,(
    ! [X14,X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v5_relat_1(X15,X14)
      | ~ v1_funct_1(X15)
      | ~ r2_hidden(X16,k1_relat_1(X15))
      | k7_partfun1(X14,X15,X16) = k1_funct_1(X15,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).

cnf(c_0_22,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X11,X12,X13] :
      ( ( ~ v1_funct_2(X13,X11,X12)
        | X11 = k1_relset_1(X11,X12,X13)
        | X12 = k1_xboole_0
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( X11 != k1_relset_1(X11,X12,X13)
        | v1_funct_2(X13,X11,X12)
        | X12 = k1_xboole_0
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( ~ v1_funct_2(X13,X11,X12)
        | X11 = k1_relset_1(X11,X12,X13)
        | X11 != k1_xboole_0
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( X11 != k1_relset_1(X11,X12,X13)
        | v1_funct_2(X13,X11,X12)
        | X11 != k1_xboole_0
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( ~ v1_funct_2(X13,X11,X12)
        | X13 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 != k1_xboole_0
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( X13 != k1_xboole_0
        | v1_funct_2(X13,X11,X12)
        | X11 = k1_xboole_0
        | X12 != k1_xboole_0
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_26,plain,(
    ! [X32,X33,X34,X35] :
      ( v1_xboole_0(X32)
      | ~ v1_funct_1(X34)
      | ~ v1_funct_2(X34,X32,X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | ~ m1_subset_1(X35,X32)
      | k3_funct_2(X32,X33,X34,X35) = k1_funct_1(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X48] :
      ( ~ v1_xboole_0(X48)
      | X48 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k3_funct_2(X1,X3,X2,X4),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,plain,
    ( k7_partfun1(X2,X1,X3) = k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_relset_1(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_38,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,esk5_1(k1_zfmisc_1(X2)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_41,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k3_funct_2(esk1_0,esk2_0,esk3_0,X1),esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_23]),c_0_33])]),c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( k7_partfun1(X1,esk3_0,X2) = k1_funct_1(esk3_0,X2)
    | ~ v5_relat_1(esk3_0,X1)
    | ~ r2_hidden(X2,k1_relset_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_33])])).

cnf(c_0_46,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_32]),c_0_23])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_48,plain,(
    ! [X56,X57,X58] :
      ( ( v4_relat_1(X58,X56)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( v5_relat_1(X58,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_49,negated_conjecture,
    ( k3_funct_2(esk1_0,esk2_0,esk3_0,X1) = k1_funct_1(esk3_0,X1)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_32]),c_0_23]),c_0_33])]),c_0_34])).

cnf(c_0_50,plain,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(k3_funct_2(esk1_0,esk2_0,esk3_0,esk5_1(esk1_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_28])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( k7_partfun1(X1,esk3_0,X2) = k1_funct_1(esk3_0,X2)
    | esk2_0 = k1_xboole_0
    | ~ v5_relat_1(esk3_0,X1)
    | ~ r2_hidden(X2,esk1_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_47]),c_0_34])).

cnf(c_0_56,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( k7_partfun1(esk2_0,esk3_0,esk4_0) != k3_funct_2(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_58,negated_conjecture,
    ( k3_funct_2(esk1_0,esk2_0,esk3_0,esk4_0) = k1_funct_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_47])).

cnf(c_0_59,plain,
    ( esk5_1(k1_zfmisc_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_50])).

cnf(c_0_60,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_43,c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k3_funct_2(esk1_0,esk2_0,esk3_0,esk5_1(esk1_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_52]),c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( k3_funct_2(esk1_0,esk2_0,esk3_0,esk5_1(esk1_0)) = k1_funct_1(esk3_0,esk5_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_28])).

cnf(c_0_63,negated_conjecture,
    ( k7_partfun1(X1,esk3_0,esk4_0) = k1_funct_1(esk3_0,esk4_0)
    | esk2_0 = k1_xboole_0
    | ~ v5_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( v5_relat_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_23])).

cnf(c_0_65,negated_conjecture,
    ( k1_funct_1(esk3_0,esk4_0) != k7_partfun1(esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_66,plain,
    ( esk5_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,esk5_1(esk1_0)),esk2_0) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_66]),c_0_60])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
