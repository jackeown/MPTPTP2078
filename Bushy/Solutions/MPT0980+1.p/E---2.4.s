%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t26_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:42 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 882 expanded)
%              Number of clauses        :   56 ( 338 expanded)
%              Number of leaves         :   14 ( 212 expanded)
%              Depth                    :   12
%              Number of atoms          :  236 (5056 expanded)
%              Number of equality atoms :   60 (1084 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t26_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & v1_funct_2(X5,X2,X3)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ( v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))
           => ( ( X3 = k1_xboole_0
                & X2 != k1_xboole_0 )
              | v2_funct_1(X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',t26_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',redefinition_k1_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',cc1_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',redefinition_k2_relset_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',redefinition_k1_partfun1)).

fof(t47_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(k5_relat_1(X2,X1))
              & r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) )
           => v2_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',t47_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',d1_funct_2)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',dt_k2_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',existence_m1_subset_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',dt_o_0_0_xboole_0)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ( ( v1_funct_1(X5)
              & v1_funct_2(X5,X2,X3)
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
           => ( v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))
             => ( ( X3 = k1_xboole_0
                  & X2 != k1_xboole_0 )
                | v2_funct_1(X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t26_funct_2])).

fof(c_0_15,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | k1_relset_1(X39,X40,X41) = k1_relat_1(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_16,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk2_0,esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & v2_funct_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0))
    & ( esk3_0 != k1_xboole_0
      | esk2_0 = k1_xboole_0 )
    & ~ v2_funct_1(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X64,X65,X66] :
      ( ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))
      | v1_relat_1(X66) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_18,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k2_relset_1(X42,X43,X44) = k2_relat_1(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_19,plain,(
    ! [X33,X34,X35,X36,X37,X38] :
      ( ~ v1_funct_1(X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | ~ v1_funct_1(X38)
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k1_partfun1(X33,X34,X35,X36,X37,X38) = k5_relat_1(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_20,plain,(
    ! [X51,X52] :
      ( ~ v1_relat_1(X51)
      | ~ v1_funct_1(X51)
      | ~ v1_relat_1(X52)
      | ~ v1_funct_1(X52)
      | ~ v2_funct_1(k5_relat_1(X52,X51))
      | ~ r1_tarski(k2_relat_1(X52),k1_relat_1(X51))
      | v2_funct_1(X52) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_funct_1])])])).

cnf(c_0_21,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X14,X15,X16] :
      ( ( ~ v1_funct_2(X16,X14,X15)
        | X14 = k1_relset_1(X14,X15,X16)
        | X15 = k1_xboole_0
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( X14 != k1_relset_1(X14,X15,X16)
        | v1_funct_2(X16,X14,X15)
        | X15 = k1_xboole_0
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( ~ v1_funct_2(X16,X14,X15)
        | X14 = k1_relset_1(X14,X15,X16)
        | X14 != k1_xboole_0
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( X14 != k1_relset_1(X14,X15,X16)
        | v1_funct_2(X16,X14,X15)
        | X14 != k1_xboole_0
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( ~ v1_funct_2(X16,X14,X15)
        | X16 = k1_xboole_0
        | X14 = k1_xboole_0
        | X15 != k1_xboole_0
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( X16 != k1_xboole_0
        | v1_funct_2(X16,X14,X15)
        | X14 = k1_xboole_0
        | X15 != k1_xboole_0
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_25,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | m1_subset_1(k2_relset_1(X26,X27,X28),k1_zfmisc_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_26,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,plain,
    ( v2_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(k5_relat_1(X2,X1))
    | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_relset_1(esk2_0,esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_33,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_35,plain,(
    ! [X49,X50] :
      ( ( ~ m1_subset_1(X49,k1_zfmisc_1(X50))
        | r1_tarski(X49,X50) )
      & ( ~ r1_tarski(X49,X50)
        | m1_subset_1(X49,k1_zfmisc_1(X50)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_36,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( k1_partfun1(X1,X2,esk2_0,esk3_0,X3,esk5_0) = k5_relat_1(X3,esk5_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_22]),c_0_29])])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_40,plain,(
    ! [X56,X57,X58] :
      ( ~ r2_hidden(X56,X57)
      | ~ m1_subset_1(X57,k1_zfmisc_1(X58))
      | ~ v1_xboole_0(X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_41,plain,(
    ! [X47,X48] :
      ( ~ m1_subset_1(X47,X48)
      | v1_xboole_0(X48)
      | r2_hidden(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_42,plain,(
    ! [X31] : m1_subset_1(esk6_1(X31),X31) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_43,negated_conjecture,
    ( v2_funct_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k1_relset_1(esk2_0,esk3_0,esk5_0))
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(k5_relat_1(X1,esk5_0))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_29])])).

cnf(c_0_44,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk5_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_22])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_27]),c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( v2_funct_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_48,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0) = k5_relat_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_27]),c_0_39])])).

fof(c_0_49,plain,(
    ! [X59] :
      ( ~ v1_xboole_0(X59)
      | X59 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( m1_subset_1(esk6_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v2_funct_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk2_0)
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(k5_relat_1(X1,esk5_0))
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_27])).

cnf(c_0_56,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    | ~ r2_hidden(X1,k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_46])).

cnf(c_0_61,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk6_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_63,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56]),c_0_39])]),c_0_57])).

cnf(c_0_64,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk6_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_52])).

cnf(c_0_66,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk4_0))
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])])).

cnf(c_0_68,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_64])).

cnf(c_0_69,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_70,plain,
    ( v1_xboole_0(esk6_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_68])])).

cnf(c_0_72,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_2(X2,k1_xboole_0,X1) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_2(esk5_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_63]),c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_63]),c_0_67])).

cnf(c_0_75,plain,
    ( esk6_1(k1_zfmisc_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( k2_relat_1(esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])])).

cnf(c_0_78,plain,
    ( r1_tarski(esk6_1(k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_52])).

cnf(c_0_79,plain,
    ( esk6_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_68])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(k5_relat_1(esk4_0,X1))
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_76]),c_0_55]),c_0_39])]),c_0_57])).

cnf(c_0_81,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_63]),c_0_67]),c_0_77])).

cnf(c_0_82,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_32]),c_0_56]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
