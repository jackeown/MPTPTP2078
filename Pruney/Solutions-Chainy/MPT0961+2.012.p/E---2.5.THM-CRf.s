%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:53 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  179 (18703 expanded)
%              Number of clauses        :  143 (8762 expanded)
%              Number of leaves         :   18 (5119 expanded)
%              Depth                    :   38
%              Number of atoms          :  414 (36257 expanded)
%              Number of equality atoms :  137 (11239 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( r2_hidden(X1,k1_relat_1(X2))
          & ! [X3] : ~ r2_hidden(X3,k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t3_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(c_0_18,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k2_relset_1(X35,X36,X37) = k2_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_19,plain,(
    ! [X38] : m1_subset_1(k6_relat_1(X38),k1_zfmisc_1(k2_zfmisc_1(X38,X38))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

fof(c_0_20,plain,(
    ! [X22] :
      ( k1_relat_1(k6_relat_1(X22)) = X22
      & k2_relat_1(k6_relat_1(X22)) = X22 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_21,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | m1_subset_1(k2_relset_1(X29,X30,X31),k1_zfmisc_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_22,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | m1_subset_1(X13,k1_zfmisc_1(X14)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_26,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k2_relset_1(X1,X1,k6_relat_1(X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

fof(c_0_28,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_xboole_0(X26)
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X26)))
      | v1_xboole_0(X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_29,plain,(
    ! [X10,X11] :
      ( ( k2_zfmisc_1(X10,X11) != k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_30,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_23]),c_0_27])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_31])).

cnf(c_0_38,plain,
    ( k2_relset_1(X1,X2,k2_zfmisc_1(X1,X2)) = k2_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_32])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_32])).

fof(c_0_40,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | r1_tarski(X21,k2_zfmisc_1(k1_relat_1(X21),k2_relat_1(X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

fof(c_0_41,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | v1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_43,plain,
    ( m1_subset_1(k2_relat_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

fof(c_0_44,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_45,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | ~ r2_hidden(X18,k1_relat_1(X19))
      | r2_hidden(esk2_2(X18,X19),k2_relat_1(X19)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t18_relat_1])])])])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( v1_xboole_0(k2_relat_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_51,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( r2_hidden(esk2_2(X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_53,plain,(
    ! [X39,X41,X42] :
      ( ( r2_hidden(esk3_1(X39),X39)
        | X39 = k1_xboole_0 )
      & ( ~ r2_hidden(X41,X39)
        | esk3_1(X39) != k4_tarski(X41,X42)
        | X39 = k1_xboole_0 )
      & ( ~ r2_hidden(X42,X39)
        | esk3_1(X39) != k4_tarski(X41,X42)
        | X39 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_32])).

cnf(c_0_56,plain,
    ( v1_xboole_0(k2_relat_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(k2_relat_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_56])).

cnf(c_0_61,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_62,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_50])])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_61])).

cnf(c_0_65,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = k1_xboole_0
    | ~ v1_xboole_0(k2_relat_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_55])).

cnf(c_0_66,plain,
    ( v1_xboole_0(k2_relat_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_43])).

cnf(c_0_67,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_63])).

cnf(c_0_68,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)
    | k1_relat_1(k2_zfmisc_1(X1,X2)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_55])).

cnf(c_0_69,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))) = k1_xboole_0
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_70,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_67]),c_0_50])])).

cnf(c_0_71,plain,
    ( r1_tarski(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)),k1_xboole_0)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_73,plain,
    ( k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)) = k1_xboole_0
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_72])).

cnf(c_0_74,plain,
    ( k2_relset_1(X1,k2_zfmisc_1(X2,X3),X4) = k2_relat_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_73])).

cnf(c_0_75,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k1_xboole_0))
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_35])).

cnf(c_0_76,plain,
    ( k2_relset_1(X1,k2_zfmisc_1(X2,X3),k6_relat_1(X4)) = X4
    | X4 != k1_xboole_0
    | ~ v1_xboole_0(X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_24])).

cnf(c_0_77,plain,
    ( m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_35])).

cnf(c_0_78,plain,
    ( k2_relset_1(X1,k1_xboole_0,k6_relat_1(X2)) = X2
    | X2 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_67]),c_0_50])])).

cnf(c_0_79,plain,
    ( k2_relset_1(X1,X2,X3) = k2_relat_1(X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_61])).

cnf(c_0_80,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | X1 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_75])).

cnf(c_0_81,plain,
    ( m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_61])).

cnf(c_0_82,plain,
    ( k2_relset_1(X1,X2,X3) = k2_relat_1(X3)
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_83,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | X3 != k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_80])).

cnf(c_0_84,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | X1 != k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_83])).

cnf(c_0_85,plain,
    ( k2_relset_1(X1,X2,k2_relat_1(X3)) = k2_relat_1(k2_relat_1(X3))
    | X3 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_84])).

cnf(c_0_86,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(X1)),k1_zfmisc_1(X2))
    | X3 != k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_85]),c_0_84])).

cnf(c_0_87,plain,
    ( v1_xboole_0(k6_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_23])).

cnf(c_0_88,plain,
    ( m1_subset_1(k2_relat_1(k2_relat_1(X1)),k1_zfmisc_1(X2))
    | X1 != k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_86])).

cnf(c_0_89,plain,
    ( r1_tarski(k6_relat_1(X1),k2_zfmisc_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_23])).

cnf(c_0_90,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_91,plain,
    ( k6_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_87])).

fof(c_0_92,plain,(
    ! [X12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X12)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_93,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | k6_relat_1(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_24])).

cnf(c_0_94,plain,
    ( r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_67])).

cnf(c_0_95,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_67]),c_0_50])])).

cnf(c_0_96,plain,
    ( k2_relset_1(X1,X2,X3) = k2_relat_1(X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_35])).

cnf(c_0_97,plain,
    ( k1_relat_1(k1_xboole_0) = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_98,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_99,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | k6_relat_1(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_93])).

cnf(c_0_100,plain,
    ( v1_xboole_0(k6_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_94])).

cnf(c_0_101,plain,
    ( v1_xboole_0(k2_relset_1(X1,k1_xboole_0,X2))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_37]),c_0_67])).

cnf(c_0_102,plain,
    ( k2_relset_1(X1,X2,X3) = k2_relat_1(X3)
    | X2 != k1_xboole_0
    | ~ r1_tarski(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_31])).

cnf(c_0_103,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_97,c_0_50])).

cnf(c_0_104,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_98])).

cnf(c_0_105,plain,
    ( k2_relat_1(k1_xboole_0) = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_91])).

cnf(c_0_106,plain,
    ( v1_relat_1(X1)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_35])).

cnf(c_0_107,plain,
    ( r1_tarski(X1,X2)
    | k6_relat_1(k6_relat_1(X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_99,c_0_24])).

cnf(c_0_108,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_100])).

cnf(c_0_109,plain,
    ( v1_xboole_0(k2_relat_1(X1))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_110,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_103]),c_0_104])])).

cnf(c_0_111,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_105,c_0_50])).

cnf(c_0_112,plain,
    ( v1_relat_1(X1)
    | X2 != k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_31])).

cnf(c_0_113,plain,
    ( k2_relset_1(X1,X2,X3) = k2_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_31])).

cnf(c_0_114,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_91]),c_0_108])])).

cnf(c_0_115,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_109])).

cnf(c_0_116,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_111]),c_0_50])])).

cnf(c_0_117,plain,
    ( v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_112])).

cnf(c_0_118,plain,
    ( v1_xboole_0(k6_relat_1(X1))
    | X1 != k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_75])).

cnf(c_0_119,plain,
    ( m1_subset_1(k2_relset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_67])).

cnf(c_0_120,plain,
    ( k2_relset_1(X1,X2,X3) = k2_relat_1(X3)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_121,plain,
    ( ~ r1_tarski(X1,k1_xboole_0)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_115]),c_0_116]),c_0_117])).

cnf(c_0_122,plain,
    ( v1_xboole_0(k6_relat_1(X1))
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_118,c_0_50])).

fof(c_0_123,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v1_funct_1(X1)
          & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    inference(assume_negation,[status(cth)],[t3_funct_2])).

cnf(c_0_124,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_95])).

cnf(c_0_125,plain,
    ( ~ r1_tarski(k6_relat_1(X1),k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_90])).

cnf(c_0_126,plain,
    ( k6_relat_1(X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_122])).

cnf(c_0_127,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_98])).

cnf(c_0_128,plain,
    ( r1_tarski(k2_relset_1(X1,X2,X3),X2)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_37])).

fof(c_0_129,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & ( ~ v1_funct_1(esk4_0)
      | ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),k2_relat_1(esk4_0))
      | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_123])])])).

fof(c_0_130,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k1_relset_1(X32,X33,X34) = k1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_131,plain,
    ( v1_xboole_0(k2_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_124])).

cnf(c_0_132,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_124,c_0_24])).

cnf(c_0_133,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_127])])).

cnf(c_0_134,plain,
    ( r1_tarski(k2_relset_1(X1,X2,X3),X2)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_128,c_0_114])).

cnf(c_0_135,negated_conjecture,
    ( ~ v1_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),k2_relat_1(esk4_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_129])).

cnf(c_0_136,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_129])).

fof(c_0_137,plain,(
    ! [X43,X44,X45] :
      ( ( ~ v1_funct_2(X45,X43,X44)
        | X43 = k1_relset_1(X43,X44,X45)
        | X44 = k1_xboole_0
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( X43 != k1_relset_1(X43,X44,X45)
        | v1_funct_2(X45,X43,X44)
        | X44 = k1_xboole_0
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( ~ v1_funct_2(X45,X43,X44)
        | X43 = k1_relset_1(X43,X44,X45)
        | X43 != k1_xboole_0
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( X43 != k1_relset_1(X43,X44,X45)
        | v1_funct_2(X45,X43,X44)
        | X43 != k1_xboole_0
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( ~ v1_funct_2(X45,X43,X44)
        | X45 = k1_xboole_0
        | X43 = k1_xboole_0
        | X44 != k1_xboole_0
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( X45 != k1_xboole_0
        | v1_funct_2(X45,X43,X44)
        | X43 = k1_xboole_0
        | X44 != k1_xboole_0
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_138,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_130])).

cnf(c_0_139,plain,
    ( v1_xboole_0(k2_relat_1(k2_relat_1(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_131,c_0_124])).

cnf(c_0_140,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_91]),c_0_98])])).

cnf(c_0_141,plain,
    ( k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_133,c_0_52])).

cnf(c_0_142,plain,
    ( v1_relat_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_31])).

cnf(c_0_143,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_134,c_0_120])).

cnf(c_0_144,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),k2_relat_1(esk4_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_136])])).

cnf(c_0_145,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_137])).

cnf(c_0_146,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_138,c_0_31])).

cnf(c_0_147,plain,
    ( v1_xboole_0(k2_relat_1(k2_relat_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_139,c_0_140])).

cnf(c_0_148,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_141,c_0_58])).

cnf(c_0_149,plain,
    ( v1_relat_1(k2_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_142,c_0_143])).

cnf(c_0_150,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_129])).

cnf(c_0_151,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),k2_relat_1(esk4_0))
    | ~ r1_tarski(esk4_0,k2_zfmisc_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_144,c_0_31])).

cnf(c_0_152,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_145,c_0_31])).

cnf(c_0_153,plain,
    ( k1_relset_1(k1_relat_1(X1),k2_relat_1(X1),X1) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_146,c_0_47])).

cnf(c_0_154,plain,
    ( k1_relset_1(X1,X1,k6_relat_1(X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_23]),c_0_90])).

cnf(c_0_155,plain,
    ( m1_subset_1(k6_relat_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_73])).

cnf(c_0_156,plain,
    ( k2_relat_1(k2_relat_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_147])).

cnf(c_0_157,plain,
    ( k1_relat_1(k2_relat_1(X1)) = k1_xboole_0
    | k2_relat_1(k2_relat_1(X1)) != k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_148,c_0_149])).

cnf(c_0_158,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_150])).

cnf(c_0_159,plain,
    ( v1_xboole_0(X1)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_95,c_0_80])).

cnf(c_0_160,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),k2_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_47]),c_0_150])])).

cnf(c_0_161,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_47]),c_0_153])).

cnf(c_0_162,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_137])).

cnf(c_0_163,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k6_relat_1(X1),X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_23]),c_0_154])])).

cnf(c_0_164,plain,
    ( v1_xboole_0(k6_relat_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_95,c_0_155])).

cnf(c_0_165,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_156,c_0_24])).

cnf(c_0_166,plain,
    ( k1_relat_1(k2_relat_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_157,c_0_156])).

cnf(c_0_167,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | k2_relat_1(esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_158,c_0_159])).

cnf(c_0_168,negated_conjecture,
    ( k2_relat_1(esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_161]),c_0_150])])).

cnf(c_0_169,plain,
    ( v1_funct_2(k6_relat_1(X1),X1,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_23]),c_0_154])]),c_0_163])).

cnf(c_0_170,plain,
    ( k6_relat_1(k2_zfmisc_1(X1,X2)) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_164])).

cnf(c_0_171,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),k1_xboole_0)
    | ~ v1_xboole_0(k6_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_160,c_0_165])).

cnf(c_0_172,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_166,c_0_24])).

cnf(c_0_173,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_167,c_0_168])])).

cnf(c_0_174,plain,
    ( v1_funct_2(k1_xboole_0,k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_169,c_0_170])).

cnf(c_0_175,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_xboole_0(k6_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_171,c_0_172])).

cnf(c_0_176,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_173])).

cnf(c_0_177,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_67]),c_0_50])])).

cnf(c_0_178,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_175,c_0_176]),c_0_177]),c_0_176]),c_0_108]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.40/0.62  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.40/0.62  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.40/0.62  #
% 0.40/0.62  # Preprocessing time       : 0.028 s
% 0.40/0.62  # Presaturation interreduction done
% 0.40/0.62  
% 0.40/0.62  # Proof found!
% 0.40/0.62  # SZS status Theorem
% 0.40/0.62  # SZS output start CNFRefutation
% 0.40/0.62  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.40/0.62  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 0.40/0.62  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.40/0.62  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.40/0.62  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.40/0.62  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.40/0.62  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.40/0.62  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.40/0.62  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 0.40/0.62  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.40/0.62  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.40/0.62  fof(t18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>~((r2_hidden(X1,k1_relat_1(X2))&![X3]:~(r2_hidden(X3,k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 0.40/0.62  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.40/0.62  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.40/0.62  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.40/0.62  fof(t3_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.40/0.62  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.40/0.62  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.40/0.62  fof(c_0_18, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|k2_relset_1(X35,X36,X37)=k2_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.40/0.62  fof(c_0_19, plain, ![X38]:m1_subset_1(k6_relat_1(X38),k1_zfmisc_1(k2_zfmisc_1(X38,X38))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.40/0.62  fof(c_0_20, plain, ![X22]:(k1_relat_1(k6_relat_1(X22))=X22&k2_relat_1(k6_relat_1(X22))=X22), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.40/0.62  fof(c_0_21, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|m1_subset_1(k2_relset_1(X29,X30,X31),k1_zfmisc_1(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.40/0.62  cnf(c_0_22, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.40/0.62  cnf(c_0_23, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.40/0.62  cnf(c_0_24, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.40/0.62  fof(c_0_25, plain, ![X13, X14]:((~m1_subset_1(X13,k1_zfmisc_1(X14))|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|m1_subset_1(X13,k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.40/0.62  cnf(c_0_26, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.40/0.62  cnf(c_0_27, plain, (k2_relset_1(X1,X1,k6_relat_1(X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.40/0.62  fof(c_0_28, plain, ![X26, X27, X28]:(~v1_xboole_0(X26)|(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X26)))|v1_xboole_0(X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.40/0.62  fof(c_0_29, plain, ![X10, X11]:((k2_zfmisc_1(X10,X11)!=k1_xboole_0|(X10=k1_xboole_0|X11=k1_xboole_0))&((X10!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0)&(X11!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.40/0.62  fof(c_0_30, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.40/0.62  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.40/0.62  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_23]), c_0_27])).
% 0.40/0.62  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.40/0.62  cnf(c_0_34, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.40/0.62  cnf(c_0_35, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.40/0.62  cnf(c_0_36, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.40/0.62  cnf(c_0_37, plain, (m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_26, c_0_31])).
% 0.40/0.62  cnf(c_0_38, plain, (k2_relset_1(X1,X2,k2_zfmisc_1(X1,X2))=k2_relat_1(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_22, c_0_32])).
% 0.40/0.62  cnf(c_0_39, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_33, c_0_32])).
% 0.40/0.62  fof(c_0_40, plain, ![X21]:(~v1_relat_1(X21)|r1_tarski(X21,k2_zfmisc_1(k1_relat_1(X21),k2_relat_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.40/0.62  fof(c_0_41, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|v1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.40/0.62  cnf(c_0_42, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.40/0.62  cnf(c_0_43, plain, (m1_subset_1(k2_relat_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.40/0.62  fof(c_0_44, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.40/0.62  fof(c_0_45, plain, ![X18, X19]:(~v1_relat_1(X19)|(~r2_hidden(X18,k1_relat_1(X19))|r2_hidden(esk2_2(X18,X19),k2_relat_1(X19)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t18_relat_1])])])])).
% 0.40/0.62  cnf(c_0_46, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_34, c_0_31])).
% 0.40/0.62  cnf(c_0_47, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.40/0.62  cnf(c_0_48, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.40/0.62  cnf(c_0_49, plain, (v1_xboole_0(k2_relat_1(k2_zfmisc_1(X1,k1_xboole_0)))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.40/0.62  cnf(c_0_50, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.40/0.62  cnf(c_0_51, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.40/0.62  cnf(c_0_52, plain, (r2_hidden(esk2_2(X2,X1),k2_relat_1(X1))|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.40/0.62  fof(c_0_53, plain, ![X39, X41, X42]:((r2_hidden(esk3_1(X39),X39)|X39=k1_xboole_0)&((~r2_hidden(X41,X39)|esk3_1(X39)!=k4_tarski(X41,X42)|X39=k1_xboole_0)&(~r2_hidden(X42,X39)|esk3_1(X39)!=k4_tarski(X41,X42)|X39=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.40/0.62  cnf(c_0_54, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.40/0.62  cnf(c_0_55, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_48, c_0_32])).
% 0.40/0.62  cnf(c_0_56, plain, (v1_xboole_0(k2_relat_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.40/0.62  cnf(c_0_57, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.40/0.62  cnf(c_0_58, plain, (r2_hidden(esk3_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.40/0.62  cnf(c_0_59, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(k2_relat_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.40/0.62  cnf(c_0_60, plain, (k2_relat_1(k2_zfmisc_1(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_56])).
% 0.40/0.62  cnf(c_0_61, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.40/0.62  cnf(c_0_62, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.40/0.62  cnf(c_0_63, plain, (v1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_50])])).
% 0.40/0.62  cnf(c_0_64, plain, (r1_tarski(X1,k1_xboole_0)|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_61])).
% 0.40/0.62  cnf(c_0_65, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=k1_xboole_0|~v1_xboole_0(k2_relat_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_62, c_0_55])).
% 0.40/0.62  cnf(c_0_66, plain, (v1_xboole_0(k2_relat_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_34, c_0_43])).
% 0.40/0.62  cnf(c_0_67, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_63])).
% 0.40/0.62  cnf(c_0_68, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)|k1_relat_1(k2_zfmisc_1(X1,X2))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_55])).
% 0.40/0.62  cnf(c_0_69, plain, (k1_relat_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))=k1_xboole_0|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.40/0.62  cnf(c_0_70, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_67]), c_0_50])])).
% 0.40/0.62  cnf(c_0_71, plain, (r1_tarski(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)),k1_xboole_0)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.40/0.62  cnf(c_0_72, plain, (v1_xboole_0(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3)))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.40/0.62  cnf(c_0_73, plain, (k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))=k1_xboole_0|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_36, c_0_72])).
% 0.40/0.62  cnf(c_0_74, plain, (k2_relset_1(X1,k2_zfmisc_1(X2,X3),X4)=k2_relat_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_22, c_0_73])).
% 0.40/0.62  cnf(c_0_75, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k1_xboole_0))|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_35])).
% 0.40/0.62  cnf(c_0_76, plain, (k2_relset_1(X1,k2_zfmisc_1(X2,X3),k6_relat_1(X4))=X4|X4!=k1_xboole_0|~v1_xboole_0(X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_24])).
% 0.40/0.62  cnf(c_0_77, plain, (m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))|X2!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_26, c_0_35])).
% 0.40/0.62  cnf(c_0_78, plain, (k2_relset_1(X1,k1_xboole_0,k6_relat_1(X2))=X2|X2!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_67]), c_0_50])])).
% 0.40/0.62  cnf(c_0_79, plain, (k2_relset_1(X1,X2,X3)=k2_relat_1(X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_22, c_0_61])).
% 0.40/0.62  cnf(c_0_80, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|X1!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_75])).
% 0.40/0.62  cnf(c_0_81, plain, (m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_26, c_0_61])).
% 0.40/0.62  cnf(c_0_82, plain, (k2_relset_1(X1,X2,X3)=k2_relat_1(X3)|X1!=k1_xboole_0|X3!=k1_xboole_0), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.40/0.62  cnf(c_0_83, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))|X3!=k1_xboole_0|X1!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_80])).
% 0.40/0.62  cnf(c_0_84, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))|X1!=k1_xboole_0), inference(er,[status(thm)],[c_0_83])).
% 0.40/0.62  cnf(c_0_85, plain, (k2_relset_1(X1,X2,k2_relat_1(X3))=k2_relat_1(k2_relat_1(X3))|X3!=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_84])).
% 0.40/0.62  cnf(c_0_86, plain, (m1_subset_1(k2_relat_1(k2_relat_1(X1)),k1_zfmisc_1(X2))|X3!=k1_xboole_0|X1!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_85]), c_0_84])).
% 0.40/0.62  cnf(c_0_87, plain, (v1_xboole_0(k6_relat_1(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_34, c_0_23])).
% 0.40/0.62  cnf(c_0_88, plain, (m1_subset_1(k2_relat_1(k2_relat_1(X1)),k1_zfmisc_1(X2))|X1!=k1_xboole_0), inference(er,[status(thm)],[c_0_86])).
% 0.40/0.62  cnf(c_0_89, plain, (r1_tarski(k6_relat_1(X1),k2_zfmisc_1(X1,X1))), inference(spm,[status(thm)],[c_0_33, c_0_23])).
% 0.40/0.62  cnf(c_0_90, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.40/0.62  cnf(c_0_91, plain, (k6_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_36, c_0_87])).
% 0.40/0.62  fof(c_0_92, plain, ![X12]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X12)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.40/0.62  cnf(c_0_93, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))|k6_relat_1(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_24])).
% 0.40/0.62  cnf(c_0_94, plain, (r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_89, c_0_67])).
% 0.40/0.62  cnf(c_0_95, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_67]), c_0_50])])).
% 0.40/0.62  cnf(c_0_96, plain, (k2_relset_1(X1,X2,X3)=k2_relat_1(X3)|X2!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_22, c_0_35])).
% 0.40/0.62  cnf(c_0_97, plain, (k1_relat_1(k1_xboole_0)=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.40/0.62  cnf(c_0_98, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.40/0.62  cnf(c_0_99, plain, (r1_tarski(k2_relat_1(X1),X2)|k6_relat_1(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_93])).
% 0.40/0.62  cnf(c_0_100, plain, (v1_xboole_0(k6_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_70, c_0_94])).
% 0.40/0.62  cnf(c_0_101, plain, (v1_xboole_0(k2_relset_1(X1,k1_xboole_0,X2))|~r1_tarski(X2,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_37]), c_0_67])).
% 0.40/0.62  cnf(c_0_102, plain, (k2_relset_1(X1,X2,X3)=k2_relat_1(X3)|X2!=k1_xboole_0|~r1_tarski(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_96, c_0_31])).
% 0.40/0.62  cnf(c_0_103, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_97, c_0_50])).
% 0.40/0.62  cnf(c_0_104, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_98])).
% 0.40/0.62  cnf(c_0_105, plain, (k2_relat_1(k1_xboole_0)=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_24, c_0_91])).
% 0.40/0.62  cnf(c_0_106, plain, (v1_relat_1(X1)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_48, c_0_35])).
% 0.40/0.62  cnf(c_0_107, plain, (r1_tarski(X1,X2)|k6_relat_1(k6_relat_1(X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_99, c_0_24])).
% 0.40/0.62  cnf(c_0_108, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_100])).
% 0.40/0.62  cnf(c_0_109, plain, (v1_xboole_0(k2_relat_1(X1))|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.40/0.62  cnf(c_0_110, plain, (~r2_hidden(X1,k1_xboole_0)|~v1_xboole_0(k2_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_103]), c_0_104])])).
% 0.40/0.62  cnf(c_0_111, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_105, c_0_50])).
% 0.40/0.62  cnf(c_0_112, plain, (v1_relat_1(X1)|X2!=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_106, c_0_31])).
% 0.40/0.62  cnf(c_0_113, plain, (k2_relset_1(X1,X2,X3)=k2_relat_1(X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_22, c_0_31])).
% 0.40/0.62  cnf(c_0_114, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_91]), c_0_108])])).
% 0.40/0.62  cnf(c_0_115, plain, (k2_relat_1(X1)=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_109])).
% 0.40/0.62  cnf(c_0_116, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_111]), c_0_50])])).
% 0.40/0.62  cnf(c_0_117, plain, (v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(er,[status(thm)],[c_0_112])).
% 0.40/0.62  cnf(c_0_118, plain, (v1_xboole_0(k6_relat_1(X1))|X1!=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_42, c_0_75])).
% 0.40/0.62  cnf(c_0_119, plain, (m1_subset_1(k2_relset_1(X1,k1_xboole_0,X2),k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_26, c_0_67])).
% 0.40/0.62  cnf(c_0_120, plain, (k2_relset_1(X1,X2,X3)=k2_relat_1(X3)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 0.40/0.62  cnf(c_0_121, plain, (~r1_tarski(X1,k1_xboole_0)|~r2_hidden(X2,k1_relat_1(X1))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_115]), c_0_116]), c_0_117])).
% 0.40/0.62  cnf(c_0_122, plain, (v1_xboole_0(k6_relat_1(X1))|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_118, c_0_50])).
% 0.40/0.62  fof(c_0_123, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))))), inference(assume_negation,[status(cth)],[t3_funct_2])).
% 0.40/0.62  cnf(c_0_124, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_95])).
% 0.40/0.62  cnf(c_0_125, plain, (~r1_tarski(k6_relat_1(X1),k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_121, c_0_90])).
% 0.40/0.62  cnf(c_0_126, plain, (k6_relat_1(X1)=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_122])).
% 0.40/0.62  cnf(c_0_127, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_98])).
% 0.40/0.62  cnf(c_0_128, plain, (r1_tarski(k2_relset_1(X1,X2,X3),X2)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_33, c_0_37])).
% 0.40/0.62  fof(c_0_129, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,k1_relat_1(esk4_0),k2_relat_1(esk4_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_123])])])).
% 0.40/0.62  fof(c_0_130, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k1_relset_1(X32,X33,X34)=k1_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.40/0.62  cnf(c_0_131, plain, (v1_xboole_0(k2_relat_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_95, c_0_124])).
% 0.40/0.62  cnf(c_0_132, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_124, c_0_24])).
% 0.40/0.62  cnf(c_0_133, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_127])])).
% 0.40/0.62  cnf(c_0_134, plain, (r1_tarski(k2_relset_1(X1,X2,X3),X2)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_128, c_0_114])).
% 0.40/0.62  cnf(c_0_135, negated_conjecture, (~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,k1_relat_1(esk4_0),k2_relat_1(esk4_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_129])).
% 0.40/0.62  cnf(c_0_136, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_129])).
% 0.40/0.62  fof(c_0_137, plain, ![X43, X44, X45]:((((~v1_funct_2(X45,X43,X44)|X43=k1_relset_1(X43,X44,X45)|X44=k1_xboole_0|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))))&(X43!=k1_relset_1(X43,X44,X45)|v1_funct_2(X45,X43,X44)|X44=k1_xboole_0|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))&((~v1_funct_2(X45,X43,X44)|X43=k1_relset_1(X43,X44,X45)|X43!=k1_xboole_0|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))))&(X43!=k1_relset_1(X43,X44,X45)|v1_funct_2(X45,X43,X44)|X43!=k1_xboole_0|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))))))&((~v1_funct_2(X45,X43,X44)|X45=k1_xboole_0|X43=k1_xboole_0|X44!=k1_xboole_0|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))))&(X45!=k1_xboole_0|v1_funct_2(X45,X43,X44)|X43=k1_xboole_0|X44!=k1_xboole_0|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.40/0.62  cnf(c_0_138, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_130])).
% 0.40/0.62  cnf(c_0_139, plain, (v1_xboole_0(k2_relat_1(k2_relat_1(X1)))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_131, c_0_124])).
% 0.40/0.62  cnf(c_0_140, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_91]), c_0_98])])).
% 0.40/0.62  cnf(c_0_141, plain, (k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_133, c_0_52])).
% 0.40/0.62  cnf(c_0_142, plain, (v1_relat_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_48, c_0_31])).
% 0.40/0.62  cnf(c_0_143, plain, (r1_tarski(k2_relat_1(X1),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_134, c_0_120])).
% 0.40/0.62  cnf(c_0_144, negated_conjecture, (~v1_funct_2(esk4_0,k1_relat_1(esk4_0),k2_relat_1(esk4_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_135, c_0_136])])).
% 0.40/0.62  cnf(c_0_145, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_137])).
% 0.40/0.62  cnf(c_0_146, plain, (k1_relset_1(X1,X2,X3)=k1_relat_1(X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_138, c_0_31])).
% 0.40/0.62  cnf(c_0_147, plain, (v1_xboole_0(k2_relat_1(k2_relat_1(X1)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_139, c_0_140])).
% 0.40/0.62  cnf(c_0_148, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_141, c_0_58])).
% 0.40/0.62  cnf(c_0_149, plain, (v1_relat_1(k2_relat_1(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_142, c_0_143])).
% 0.40/0.62  cnf(c_0_150, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_129])).
% 0.40/0.62  cnf(c_0_151, negated_conjecture, (~v1_funct_2(esk4_0,k1_relat_1(esk4_0),k2_relat_1(esk4_0))|~r1_tarski(esk4_0,k2_zfmisc_1(k1_relat_1(esk4_0),k2_relat_1(esk4_0)))), inference(spm,[status(thm)],[c_0_144, c_0_31])).
% 0.40/0.62  cnf(c_0_152, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relset_1(X3,X1,X2)!=X3|~r1_tarski(X2,k2_zfmisc_1(X3,X1))), inference(spm,[status(thm)],[c_0_145, c_0_31])).
% 0.40/0.62  cnf(c_0_153, plain, (k1_relset_1(k1_relat_1(X1),k2_relat_1(X1),X1)=k1_relat_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_146, c_0_47])).
% 0.40/0.62  cnf(c_0_154, plain, (k1_relset_1(X1,X1,k6_relat_1(X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_23]), c_0_90])).
% 0.40/0.62  cnf(c_0_155, plain, (m1_subset_1(k6_relat_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_23, c_0_73])).
% 0.40/0.62  cnf(c_0_156, plain, (k2_relat_1(k2_relat_1(X1))=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_36, c_0_147])).
% 0.40/0.62  cnf(c_0_157, plain, (k1_relat_1(k2_relat_1(X1))=k1_xboole_0|k2_relat_1(k2_relat_1(X1))!=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_148, c_0_149])).
% 0.40/0.62  cnf(c_0_158, negated_conjecture, (v1_xboole_0(esk4_0)|~v1_xboole_0(k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_54, c_0_150])).
% 0.40/0.62  cnf(c_0_159, plain, (v1_xboole_0(X1)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_95, c_0_80])).
% 0.40/0.62  cnf(c_0_160, negated_conjecture, (~v1_funct_2(esk4_0,k1_relat_1(esk4_0),k2_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_47]), c_0_150])])).
% 0.40/0.62  cnf(c_0_161, plain, (k2_relat_1(X1)=k1_xboole_0|v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_47]), c_0_153])).
% 0.40/0.62  cnf(c_0_162, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_137])).
% 0.40/0.62  cnf(c_0_163, plain, (X1=k1_xboole_0|v1_funct_2(k6_relat_1(X1),X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_23]), c_0_154])])).
% 0.40/0.62  cnf(c_0_164, plain, (v1_xboole_0(k6_relat_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_95, c_0_155])).
% 0.40/0.62  cnf(c_0_165, plain, (k2_relat_1(X1)=k1_xboole_0|~v1_xboole_0(k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_156, c_0_24])).
% 0.40/0.62  cnf(c_0_166, plain, (k1_relat_1(k2_relat_1(X1))=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_157, c_0_156])).
% 0.40/0.62  cnf(c_0_167, negated_conjecture, (v1_xboole_0(esk4_0)|k2_relat_1(esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_158, c_0_159])).
% 0.40/0.62  cnf(c_0_168, negated_conjecture, (k2_relat_1(esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_161]), c_0_150])])).
% 0.40/0.62  cnf(c_0_169, plain, (v1_funct_2(k6_relat_1(X1),X1,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_23]), c_0_154])]), c_0_163])).
% 0.40/0.62  cnf(c_0_170, plain, (k6_relat_1(k2_zfmisc_1(X1,X2))=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_36, c_0_164])).
% 0.40/0.62  cnf(c_0_171, negated_conjecture, (~v1_funct_2(esk4_0,k1_relat_1(esk4_0),k1_xboole_0)|~v1_xboole_0(k6_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_160, c_0_165])).
% 0.40/0.62  cnf(c_0_172, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_xboole_0(k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_166, c_0_24])).
% 0.40/0.62  cnf(c_0_173, negated_conjecture, (v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_167, c_0_168])])).
% 0.40/0.62  cnf(c_0_174, plain, (v1_funct_2(k1_xboole_0,k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_169, c_0_170])).
% 0.40/0.62  cnf(c_0_175, negated_conjecture, (~v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)|~v1_xboole_0(k6_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_171, c_0_172])).
% 0.40/0.62  cnf(c_0_176, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_173])).
% 0.40/0.62  cnf(c_0_177, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_67]), c_0_50])])).
% 0.40/0.62  cnf(c_0_178, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_175, c_0_176]), c_0_177]), c_0_176]), c_0_108]), c_0_50])]), ['proof']).
% 0.40/0.62  # SZS output end CNFRefutation
% 0.40/0.62  # Proof object total steps             : 179
% 0.40/0.62  # Proof object clause steps            : 143
% 0.40/0.62  # Proof object formula steps           : 36
% 0.40/0.62  # Proof object conjectures             : 17
% 0.40/0.62  # Proof object clause conjectures      : 14
% 0.40/0.62  # Proof object formula conjectures     : 3
% 0.40/0.62  # Proof object initial clauses used    : 24
% 0.40/0.62  # Proof object initial formulas used   : 18
% 0.40/0.62  # Proof object generating inferences   : 115
% 0.40/0.62  # Proof object simplifying inferences  : 55
% 0.40/0.62  # Training examples: 0 positive, 0 negative
% 0.40/0.62  # Parsed axioms                        : 19
% 0.40/0.62  # Removed by relevancy pruning/SinE    : 0
% 0.40/0.62  # Initial clauses                      : 33
% 0.40/0.62  # Removed in clause preprocessing      : 0
% 0.40/0.62  # Initial clauses in saturation        : 33
% 0.40/0.62  # Processed clauses                    : 3426
% 0.40/0.62  # ...of these trivial                  : 58
% 0.40/0.62  # ...subsumed                          : 2468
% 0.40/0.62  # ...remaining for further processing  : 900
% 0.40/0.62  # Other redundant clauses eliminated   : 0
% 0.40/0.62  # Clauses deleted for lack of memory   : 0
% 0.40/0.62  # Backward-subsumed                    : 144
% 0.40/0.62  # Backward-rewritten                   : 66
% 0.40/0.62  # Generated clauses                    : 26589
% 0.40/0.62  # ...of the previous two non-trivial   : 17424
% 0.40/0.62  # Contextual simplify-reflections      : 40
% 0.40/0.62  # Paramodulations                      : 26581
% 0.40/0.62  # Factorizations                       : 0
% 0.40/0.62  # Equation resolutions                 : 8
% 0.40/0.62  # Propositional unsat checks           : 0
% 0.40/0.62  #    Propositional check models        : 0
% 0.40/0.62  #    Propositional check unsatisfiable : 0
% 0.40/0.62  #    Propositional clauses             : 0
% 0.40/0.62  #    Propositional clauses after purity: 0
% 0.40/0.62  #    Propositional unsat core size     : 0
% 0.40/0.62  #    Propositional preprocessing time  : 0.000
% 0.40/0.62  #    Propositional encoding time       : 0.000
% 0.40/0.62  #    Propositional solver time         : 0.000
% 0.40/0.62  #    Success case prop preproc time    : 0.000
% 0.40/0.62  #    Success case prop encoding time   : 0.000
% 0.40/0.62  #    Success case prop solver time     : 0.000
% 0.40/0.62  # Current number of processed clauses  : 657
% 0.40/0.62  #    Positive orientable unit clauses  : 35
% 0.40/0.62  #    Positive unorientable unit clauses: 4
% 0.40/0.62  #    Negative unit clauses             : 1
% 0.40/0.62  #    Non-unit-clauses                  : 617
% 0.40/0.62  # Current number of unprocessed clauses: 13792
% 0.40/0.62  # ...number of literals in the above   : 47511
% 0.40/0.62  # Current number of archived formulas  : 0
% 0.40/0.62  # Current number of archived clauses   : 243
% 0.40/0.62  # Clause-clause subsumption calls (NU) : 103389
% 0.40/0.62  # Rec. Clause-clause subsumption calls : 79813
% 0.40/0.62  # Non-unit clause-clause subsumptions  : 2340
% 0.40/0.62  # Unit Clause-clause subsumption calls : 630
% 0.40/0.62  # Rewrite failures with RHS unbound    : 0
% 0.40/0.62  # BW rewrite match attempts            : 126
% 0.40/0.62  # BW rewrite match successes           : 20
% 0.40/0.62  # Condensation attempts                : 0
% 0.40/0.62  # Condensation successes               : 0
% 0.40/0.62  # Termbank termtop insertions          : 283403
% 0.40/0.62  
% 0.40/0.62  # -------------------------------------------------
% 0.40/0.62  # User time                : 0.265 s
% 0.40/0.62  # System time              : 0.011 s
% 0.40/0.62  # Total time               : 0.276 s
% 0.40/0.62  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
