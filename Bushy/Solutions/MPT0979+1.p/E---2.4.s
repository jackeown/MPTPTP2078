%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t25_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:42 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   75 (1155 expanded)
%              Number of clauses        :   51 ( 455 expanded)
%              Number of leaves         :   12 ( 287 expanded)
%              Depth                    :   16
%              Number of atoms          :  261 (7329 expanded)
%              Number of equality atoms :   82 (2206 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => ( v2_funct_1(X3)
        <=> ! [X4,X5] :
              ( ( r2_hidden(X4,X1)
                & r2_hidden(X5,X1)
                & k1_funct_1(X3,X4) = k1_funct_1(X3,X5) )
             => X4 = X5 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t25_funct_2.p',t25_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t25_funct_2.p',redefinition_k1_relset_1)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t25_funct_2.p',dt_k1_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t25_funct_2.p',cc1_relset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t25_funct_2.p',t5_subset)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t25_funct_2.p',t7_boole)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t25_funct_2.p',t4_subset)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t25_funct_2.p',d8_funct_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t25_funct_2.p',t2_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t25_funct_2.p',t6_boole)).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t25_funct_2.p',d1_funct_2)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t25_funct_2.p',dt_o_0_0_xboole_0)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v2_funct_1(X3)
          <=> ! [X4,X5] :
                ( ( r2_hidden(X4,X1)
                  & r2_hidden(X5,X1)
                  & k1_funct_1(X3,X4) = k1_funct_1(X3,X5) )
               => X4 = X5 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_funct_2])).

fof(c_0_13,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | k1_relset_1(X28,X29,X30) = k1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_14,negated_conjecture,(
    ! [X11,X12] :
      ( v1_funct_1(esk3_0)
      & v1_funct_2(esk3_0,esk1_0,esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
      & ( esk2_0 != k1_xboole_0
        | esk1_0 = k1_xboole_0 )
      & ( r2_hidden(esk4_0,esk1_0)
        | ~ v2_funct_1(esk3_0) )
      & ( r2_hidden(esk5_0,esk1_0)
        | ~ v2_funct_1(esk3_0) )
      & ( k1_funct_1(esk3_0,esk4_0) = k1_funct_1(esk3_0,esk5_0)
        | ~ v2_funct_1(esk3_0) )
      & ( esk4_0 != esk5_0
        | ~ v2_funct_1(esk3_0) )
      & ( v2_funct_1(esk3_0)
        | ~ r2_hidden(X11,esk1_0)
        | ~ r2_hidden(X12,esk1_0)
        | k1_funct_1(esk3_0,X11) != k1_funct_1(esk3_0,X12)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])])).

fof(c_0_15,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | m1_subset_1(k1_relset_1(X23,X24,X25),k1_zfmisc_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_16,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | v1_relat_1(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_19,plain,(
    ! [X40,X41,X42] :
      ( ~ r2_hidden(X40,X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(X42))
      | ~ v1_xboole_0(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_20,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_22,plain,(
    ! [X44,X45] :
      ( ~ r2_hidden(X44,X45)
      | ~ v1_xboole_0(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_23,plain,(
    ! [X37,X38,X39] :
      ( ~ r2_hidden(X37,X38)
      | ~ m1_subset_1(X38,k1_zfmisc_1(X39))
      | m1_subset_1(X37,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_24,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v2_funct_1(X18)
        | ~ r2_hidden(X19,k1_relat_1(X18))
        | ~ r2_hidden(X20,k1_relat_1(X18))
        | k1_funct_1(X18,X19) != k1_funct_1(X18,X20)
        | X19 = X20
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( r2_hidden(esk6_1(X18),k1_relat_1(X18))
        | v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( r2_hidden(esk7_1(X18),k1_relat_1(X18))
        | v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( k1_funct_1(X18,esk6_1(X18)) = k1_funct_1(X18,esk7_1(X18))
        | v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( esk6_1(X18) != esk7_1(X18)
        | v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_25,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_17])])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk5_0,esk1_0)
    | ~ v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( v2_funct_1(esk3_0)
    | X1 = X2
    | ~ r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X2,esk1_0)
    | k1_funct_1(esk3_0,X1) != k1_funct_1(esk3_0,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,plain,
    ( k1_funct_1(X1,esk6_1(X1)) = k1_funct_1(X1,esk7_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_17])).

fof(c_0_35,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X33,X34)
      | v1_xboole_0(X34)
      | r2_hidden(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( r2_hidden(esk7_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    | ~ v2_funct_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(X1,esk1_0)
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_40,plain,
    ( r2_hidden(esk6_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_41,plain,(
    ! [X43] :
      ( ~ v1_xboole_0(X43)
      | X43 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_42,negated_conjecture,
    ( esk6_1(esk3_0) = X1
    | v2_funct_1(esk3_0)
    | k1_funct_1(esk3_0,esk7_1(esk3_0)) != k1_funct_1(esk3_0,X1)
    | ~ r2_hidden(esk6_1(esk3_0),esk1_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),c_0_34])])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_34]),c_0_33])]),c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( v2_funct_1(esk3_0)
    | m1_subset_1(esk6_1(esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_34]),c_0_33])])).

fof(c_0_46,plain,(
    ! [X15,X16,X17] :
      ( ( ~ v1_funct_2(X17,X15,X16)
        | X15 = k1_relset_1(X15,X16,X17)
        | X16 = k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( X15 != k1_relset_1(X15,X16,X17)
        | v1_funct_2(X17,X15,X16)
        | X16 = k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( ~ v1_funct_2(X17,X15,X16)
        | X15 = k1_relset_1(X15,X16,X17)
        | X15 != k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( X15 != k1_relset_1(X15,X16,X17)
        | v1_funct_2(X17,X15,X16)
        | X15 != k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( ~ v1_funct_2(X17,X15,X16)
        | X17 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 != k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( X17 != k1_xboole_0
        | v1_funct_2(X17,X15,X16)
        | X15 = k1_xboole_0
        | X16 != k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_49,negated_conjecture,
    ( esk6_1(esk3_0) = X1
    | v2_funct_1(esk3_0)
    | k1_funct_1(esk3_0,esk7_1(esk3_0)) != k1_funct_1(esk3_0,X1)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_50,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( esk6_1(esk3_0) = esk7_1(esk3_0)
    | v2_funct_1(esk3_0)
    | ~ r2_hidden(esk7_1(esk3_0),esk1_0) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( v2_funct_1(esk3_0)
    | m1_subset_1(esk7_1(esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_37]),c_0_34]),c_0_33])])).

cnf(c_0_54,plain,
    ( k1_relset_1(X1,X2,X3) = X1
    | X2 = o_0_0_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X3,X1,X2) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_56,plain,
    ( v2_funct_1(X1)
    | esk6_1(X1) != esk7_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( esk6_1(esk3_0) = esk7_1(esk3_0)
    | v2_funct_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_43]),c_0_44]),c_0_53])).

cnf(c_0_58,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_59,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0
    | esk2_0 = o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_17]),c_0_21]),c_0_55])])).

cnf(c_0_60,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_34]),c_0_33])])).

cnf(c_0_61,negated_conjecture,
    ( k1_funct_1(esk3_0,esk4_0) = k1_funct_1(esk3_0,esk5_0)
    | ~ v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_62,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | X1 = X2
    | k1_funct_1(esk3_0,X1) != k1_funct_1(esk3_0,X2)
    | ~ r2_hidden(X2,esk1_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_34]),c_0_33])]),c_0_60])])).

cnf(c_0_63,negated_conjecture,
    ( k1_funct_1(esk3_0,esk5_0) = k1_funct_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_60])])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk5_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_60])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_0)
    | ~ v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_66,negated_conjecture,
    ( esk4_0 != esk5_0
    | ~ v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_67,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_68,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | X1 = esk5_0
    | k1_funct_1(esk3_0,X1) != k1_funct_1(esk3_0,esk4_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_60])])).

cnf(c_0_70,negated_conjecture,
    ( esk5_0 != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_60])])).

cnf(c_0_71,negated_conjecture,
    ( esk1_0 = o_0_0_xboole_0
    | esk2_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_51]),c_0_51])).

cnf(c_0_72,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_68]),c_0_69])]),c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( esk1_0 = o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72])])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_73]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
