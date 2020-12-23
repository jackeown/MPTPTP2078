%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t16_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:35 EDT 2019

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  114 (1325 expanded)
%              Number of clauses        :   78 ( 596 expanded)
%              Number of leaves         :   18 ( 332 expanded)
%              Depth                    :   20
%              Number of atoms          :  349 (5071 expanded)
%              Number of equality atoms :   94 (1303 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',t5_subset)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',dt_k2_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',redefinition_k2_relset_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',existence_m1_subset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',t8_boole)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',cc4_relset_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',dt_o_0_0_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',t2_subset)).

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
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',t16_funct_2)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',t6_boole)).

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
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',d5_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',cc1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',d1_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',redefinition_k1_relset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',t7_boole)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',t2_tarski)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',t4_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t16_funct_2.p',t1_subset)).

fof(c_0_18,plain,(
    ! [X52,X53,X54] :
      ( ~ r2_hidden(X52,X53)
      | ~ m1_subset_1(X53,k1_zfmisc_1(X54))
      | ~ v1_xboole_0(X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_19,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | m1_subset_1(k2_relset_1(X29,X30,X31),k1_zfmisc_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

fof(c_0_20,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k2_relset_1(X37,X38,X39) = k2_relat_1(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_21,plain,(
    ! [X32] : m1_subset_1(esk8_1(X32),X32) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_22,plain,(
    ! [X58,X59] :
      ( ~ v1_xboole_0(X58)
      | X58 = X59
      | ~ v1_xboole_0(X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_23,plain,(
    ! [X63,X64,X65] :
      ( ~ v1_xboole_0(X63)
      | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X64,X63)))
      | v1_xboole_0(X65) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk8_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k2_relset_1(X3,X1,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( k2_relset_1(X1,X2,esk8_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) = k2_relat_1(esk8_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( X1 = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( v1_xboole_0(esk8_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k2_relat_1(esk8_1(k1_zfmisc_1(k2_zfmisc_1(X3,X1))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_27])])).

cnf(c_0_36,plain,
    ( esk8_1(k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = o_0_0_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_37,plain,(
    ! [X42,X43] :
      ( ~ m1_subset_1(X42,X43)
      | v1_xboole_0(X43)
      | r2_hidden(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_38,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k2_relat_1(o_0_0_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_40,negated_conjecture,(
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

fof(c_0_41,plain,(
    ! [X55] :
      ( ~ v1_xboole_0(X55)
      | X55 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_42,plain,
    ( v1_xboole_0(k2_relat_1(o_0_0_xboole_0))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k2_relat_1(o_0_0_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_43,plain,(
    ! [X16,X17,X18,X20,X21,X22,X24] :
      ( ( r2_hidden(esk5_3(X16,X17,X18),k1_relat_1(X16))
        | ~ r2_hidden(X18,X17)
        | X17 != k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( X18 = k1_funct_1(X16,esk5_3(X16,X17,X18))
        | ~ r2_hidden(X18,X17)
        | X17 != k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(X21,k1_relat_1(X16))
        | X20 != k1_funct_1(X16,X21)
        | r2_hidden(X20,X17)
        | X17 != k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(esk6_2(X16,X22),X22)
        | ~ r2_hidden(X24,k1_relat_1(X16))
        | esk6_2(X16,X22) != k1_funct_1(X16,X24)
        | X22 = k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(esk7_2(X16,X22),k1_relat_1(X16))
        | r2_hidden(esk6_2(X16,X22),X22)
        | X22 = k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( esk6_2(X16,X22) = k1_funct_1(X16,esk7_2(X16,X22))
        | r2_hidden(esk6_2(X16,X22),X22)
        | X22 = k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_44,plain,(
    ! [X60,X61,X62] :
      ( ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
      | v1_relat_1(X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_45,negated_conjecture,(
    ! [X9] :
      ( v1_funct_1(esk3_0)
      & v1_funct_2(esk3_0,esk1_0,esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
      & ( r2_hidden(esk4_1(X9),esk1_0)
        | ~ r2_hidden(X9,esk2_0) )
      & ( X9 = k1_funct_1(esk3_0,esk4_1(X9))
        | ~ r2_hidden(X9,esk2_0) )
      & k2_relset_1(esk1_0,esk2_0,esk3_0) != esk2_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])])])).

fof(c_0_46,plain,(
    ! [X13,X14,X15] :
      ( ( ~ v1_funct_2(X15,X13,X14)
        | X13 = k1_relset_1(X13,X14,X15)
        | X14 = k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( X13 != k1_relset_1(X13,X14,X15)
        | v1_funct_2(X15,X13,X14)
        | X14 = k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( ~ v1_funct_2(X15,X13,X14)
        | X13 = k1_relset_1(X13,X14,X15)
        | X13 != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( X13 != k1_relset_1(X13,X14,X15)
        | v1_funct_2(X15,X13,X14)
        | X13 != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( ~ v1_funct_2(X15,X13,X14)
        | X15 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( X15 != k1_xboole_0
        | v1_funct_2(X15,X13,X14)
        | X13 = k1_xboole_0
        | X14 != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_48,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k1_relset_1(X34,X35,X36) = k1_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_49,plain,
    ( v1_xboole_0(k2_relat_1(o_0_0_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_27])).

cnf(c_0_50,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_29])).

cnf(c_0_55,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( v1_xboole_0(k2_relat_1(o_0_0_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_29])).

fof(c_0_57,plain,(
    ! [X56,X57] :
      ( ~ r2_hidden(X56,X57)
      | ~ v1_xboole_0(X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_58,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_59,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])])).

cnf(c_0_60,negated_conjecture,
    ( X1 = k1_funct_1(esk3_0,esk4_1(X1))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_61,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_63,plain,
    ( k1_relset_1(X1,X2,X3) = X1
    | X2 = o_0_0_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X3,X1,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_66,plain,
    ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_56])).

fof(c_0_67,plain,(
    ! [X44,X45] :
      ( ( ~ r2_hidden(esk9_2(X44,X45),X44)
        | ~ r2_hidden(esk9_2(X44,X45),X45)
        | X44 = X45 )
      & ( r2_hidden(esk9_2(X44,X45),X44)
        | r2_hidden(esk9_2(X44,X45),X45)
        | X44 = X45 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,plain,
    ( r2_hidden(esk5_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk3_0))
    | ~ r2_hidden(esk4_1(X1),k1_relat_1(esk3_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62])])).

cnf(c_0_71,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0
    | esk2_0 = o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_52]),c_0_64]),c_0_65])])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk4_1(X1),esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_73,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_52])).

cnf(c_0_74,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,o_0_0_xboole_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_66])).

cnf(c_0_75,plain,
    ( r2_hidden(esk9_2(X1,X2),X1)
    | r2_hidden(esk9_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,plain,
    ( ~ v1_xboole_0(k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | r2_hidden(X1,k2_relat_1(esk3_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_73]),c_0_52])])).

cnf(c_0_79,plain,
    ( o_0_0_xboole_0 = X1
    | r2_hidden(esk9_2(o_0_0_xboole_0,X1),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | ~ v1_xboole_0(k1_relat_1(esk3_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_61]),c_0_62])])).

cnf(c_0_81,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    | ~ r2_hidden(X1,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_78])).

fof(c_0_82,plain,(
    ! [X49,X50,X51] :
      ( ~ r2_hidden(X49,X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(X51))
      | m1_subset_1(X49,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_83,plain,(
    ! [X40,X41] :
      ( ~ r2_hidden(X40,X41)
      | m1_subset_1(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_84,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_85,plain,
    ( o_0_0_xboole_0 = X1
    | r2_hidden(esk9_2(o_0_0_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_29])).

cnf(c_0_86,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | ~ v1_xboole_0(k1_relat_1(esk3_0))
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_39]),c_0_33])).

cnf(c_0_87,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_59]),c_0_61]),c_0_62])])).

cnf(c_0_88,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_89,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_90,plain,
    ( X1 = X2
    | ~ r2_hidden(esk9_2(X1,X2),X1)
    | ~ r2_hidden(esk9_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_91,negated_conjecture,
    ( k2_relat_1(esk3_0) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_84,c_0_73])).

cnf(c_0_92,plain,
    ( k2_relat_1(X1) = o_0_0_xboole_0
    | ~ v1_xboole_0(k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | ~ v1_xboole_0(k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_27])).

cnf(c_0_94,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk3_0))
    | ~ v1_xboole_0(esk2_0)
    | ~ m1_subset_1(X1,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_39])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(X1,esk2_0)
    | ~ r2_hidden(X1,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_78])).

cnf(c_0_96,plain,
    ( X1 = X2
    | r2_hidden(esk9_2(X1,X2),X1)
    | m1_subset_1(esk9_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_89,c_0_75])).

cnf(c_0_97,plain,
    ( X1 = X2
    | v1_xboole_0(X2)
    | ~ r2_hidden(esk9_2(X1,X2),X1)
    | ~ m1_subset_1(esk9_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_90,c_0_39])).

cnf(c_0_98,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_61]),c_0_62])]),c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk3_0))
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_27])).

cnf(c_0_100,negated_conjecture,
    ( k2_relat_1(esk3_0) = X1
    | m1_subset_1(esk9_2(k2_relat_1(esk3_0),X1),esk2_0)
    | m1_subset_1(esk9_2(k2_relat_1(esk3_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_101,negated_conjecture,
    ( k2_relat_1(esk3_0) = X1
    | esk2_0 = o_0_0_xboole_0
    | v1_xboole_0(X1)
    | ~ r2_hidden(esk9_2(k2_relat_1(esk3_0),X1),esk2_0)
    | ~ m1_subset_1(esk9_2(k2_relat_1(esk3_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_77])).

cnf(c_0_102,plain,
    ( X1 = X2
    | r2_hidden(esk9_2(X1,X2),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_75])).

cnf(c_0_103,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_104,plain,
    ( X1 = X2
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(esk9_2(X1,X2),X2)
    | ~ m1_subset_1(esk9_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_39])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(esk9_2(k2_relat_1(esk3_0),esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_100]),c_0_91])).

cnf(c_0_106,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | ~ v1_xboole_0(k2_relat_1(esk3_0))
    | ~ m1_subset_1(esk9_2(k2_relat_1(esk3_0),esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_91]),c_0_103])).

cnf(c_0_107,plain,
    ( X1 = X2
    | m1_subset_1(esk9_2(X1,X2),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_96])).

cnf(c_0_108,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk3_0))
    | ~ m1_subset_1(esk9_2(k2_relat_1(esk3_0),esk2_0),k2_relat_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_91]),c_0_103])).

cnf(c_0_109,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | m1_subset_1(X1,k2_relat_1(esk3_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_77])).

cnf(c_0_110,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | ~ v1_xboole_0(k2_relat_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_91])).

cnf(c_0_111,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | ~ r2_hidden(esk9_2(k2_relat_1(esk3_0),esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_110])).

cnf(c_0_112,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_39]),c_0_105])]),c_0_103])).

cnf(c_0_113,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_112]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
