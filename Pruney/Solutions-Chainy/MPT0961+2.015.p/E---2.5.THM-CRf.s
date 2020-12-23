%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:53 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  132 (1675 expanded)
%              Number of clauses        :   96 ( 791 expanded)
%              Number of leaves         :   18 ( 434 expanded)
%              Depth                    :   23
%              Number of atoms          :  361 (4370 expanded)
%              Number of equality atoms :  129 (1094 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t3_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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

fof(c_0_18,plain,(
    ! [X33,X34] :
      ( ~ r2_hidden(X33,X34)
      | ~ r1_tarski(X34,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_19,plain,(
    ! [X17,X18,X19,X21,X22,X23,X24,X26] :
      ( ( ~ r2_hidden(X19,X18)
        | r2_hidden(k4_tarski(X19,esk2_3(X17,X18,X19)),X17)
        | X18 != k1_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(X21,X22),X17)
        | r2_hidden(X21,X18)
        | X18 != k1_relat_1(X17) )
      & ( ~ r2_hidden(esk3_2(X23,X24),X24)
        | ~ r2_hidden(k4_tarski(esk3_2(X23,X24),X26),X23)
        | X24 = k1_relat_1(X23) )
      & ( r2_hidden(esk3_2(X23,X24),X24)
        | r2_hidden(k4_tarski(esk3_2(X23,X24),esk4_2(X23,X24)),X23)
        | X24 = k1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_22,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_23,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | v1_relat_1(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_24,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | m1_subset_1(X13,k1_zfmisc_1(X14)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_25,plain,
    ( X1 != k1_relat_1(X2)
    | ~ r1_tarski(X2,k4_tarski(X3,esk2_3(X2,X1,X3)))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v1_funct_1(X1)
          & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    inference(assume_negation,[status(cth)],[t3_funct_2])).

fof(c_0_30,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_xboole_0(X35)
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X36,X35)))
      | v1_xboole_0(X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_31,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_32,plain,
    ( X1 != k1_relat_1(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_33,plain,(
    ! [X6] :
      ( X6 = k1_xboole_0
      | r2_hidden(esk1_1(X6),X6) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_34,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_35,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & ( ~ v1_funct_1(esk5_0)
      | ~ v1_funct_2(esk5_0,k1_relat_1(esk5_0),k2_relat_1(esk5_0))
      | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),k2_relat_1(esk5_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X28] :
      ( ~ v1_relat_1(X28)
      | r1_tarski(X28,k2_zfmisc_1(k1_relat_1(X28),k2_relat_1(X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

fof(c_0_39,plain,(
    ! [X11,X12] :
      ( ( k2_zfmisc_1(X11,X12) != k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_40,plain,(
    ! [X29,X30] :
      ( ( r1_tarski(k1_relat_1(X29),k1_relat_1(X30))
        | ~ r1_tarski(X29,X30)
        | ~ v1_relat_1(X30)
        | ~ v1_relat_1(X29) )
      & ( r1_tarski(k2_relat_1(X29),k2_relat_1(X30))
        | ~ r1_tarski(X29,X30)
        | ~ v1_relat_1(X30)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_26])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_45,plain,(
    ! [X31] :
      ( k1_relat_1(k6_relat_1(X31)) = X31
      & k2_relat_1(k6_relat_1(X31)) = X31 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_46,plain,(
    ! [X32] :
      ( v1_relat_1(k6_relat_1(X32))
      & v1_funct_1(k6_relat_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_47,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | X5 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_55,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_relat_1(X1),k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_62,plain,
    ( r1_tarski(k6_relat_1(X1),k2_zfmisc_1(X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_55]),c_0_56]),c_0_57])])).

cnf(c_0_63,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_65,plain,
    ( r1_tarski(k6_relat_1(X1),k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_57]),c_0_55])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(k6_relat_1(X1),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_57]),c_0_56])).

cnf(c_0_67,plain,
    ( r1_tarski(k6_relat_1(X1),k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,plain,
    ( k6_relat_1(X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_26])])).

cnf(c_0_69,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_32,c_0_53])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,plain,
    ( k2_relat_1(k1_xboole_0) = X1
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_68])).

cnf(c_0_72,plain,
    ( X1 != k1_relat_1(X2)
    | X2 != k1_xboole_0
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_21])).

cnf(c_0_73,plain,
    ( k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_50])).

cnf(c_0_74,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_59])).

cnf(c_0_75,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_71])).

cnf(c_0_76,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | X1 != k1_relat_1(X2)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_42])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_68]),c_0_26])])).

cnf(c_0_79,plain,
    ( X1 != k1_relat_1(X2)
    | X3 != k1_relat_1(X1)
    | X2 != k1_xboole_0
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_72,c_0_21])).

cnf(c_0_80,plain,
    ( v1_xboole_0(k6_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_62])).

cnf(c_0_81,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_53]),c_0_75]),c_0_54]),c_0_75]),c_0_76])])).

cnf(c_0_82,plain,
    ( v1_relat_1(k1_relat_1(X1))
    | ~ v1_relat_1(k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_52]),c_0_34])).

cnf(c_0_83,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_84,plain,
    ( v1_relat_1(X1)
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_78]),c_0_54])])).

cnf(c_0_85,plain,
    ( X1 = k1_xboole_0
    | X2 != k1_relat_1(X3)
    | X1 != k1_relat_1(X2)
    | X3 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_42])).

cnf(c_0_86,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_56]),c_0_57])])).

cnf(c_0_87,plain,
    ( k6_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_80])).

cnf(c_0_88,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_81]),c_0_76])])).

cnf(c_0_89,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_90,plain,
    ( v1_relat_1(k1_relat_1(X1))
    | X2 != k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_54])]),c_0_84])).

cnf(c_0_91,plain,
    ( X1 = k1_xboole_0
    | X1 != k1_relat_1(k1_relat_1(X2))
    | X2 != k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_85])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_57]),c_0_56])).

cnf(c_0_93,plain,
    ( k6_relat_1(X1) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_89])).

cnf(c_0_95,plain,
    ( v1_relat_1(k1_relat_1(X1))
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_90,c_0_78])).

cnf(c_0_96,plain,
    ( k1_relat_1(k1_relat_1(X1)) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_91])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_26])])).

cnf(c_0_98,plain,
    ( r1_tarski(k1_relat_1(X1),k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96])).

cnf(c_0_99,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_100,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | X1 != k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_99])).

cnf(c_0_101,negated_conjecture,
    ( ~ v1_funct_1(esk5_0)
    | ~ v1_funct_2(esk5_0,k1_relat_1(esk5_0),k2_relat_1(esk5_0))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),k2_relat_1(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_102,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_103,plain,(
    ! [X41,X42,X43] :
      ( ( ~ v1_funct_2(X43,X41,X42)
        | X41 = k1_relset_1(X41,X42,X43)
        | X42 = k1_xboole_0
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( X41 != k1_relset_1(X41,X42,X43)
        | v1_funct_2(X43,X41,X42)
        | X42 = k1_xboole_0
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( ~ v1_funct_2(X43,X41,X42)
        | X41 = k1_relset_1(X41,X42,X43)
        | X41 != k1_xboole_0
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( X41 != k1_relset_1(X41,X42,X43)
        | v1_funct_2(X43,X41,X42)
        | X41 != k1_xboole_0
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( ~ v1_funct_2(X43,X41,X42)
        | X43 = k1_xboole_0
        | X41 = k1_xboole_0
        | X42 != k1_xboole_0
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( X43 != k1_xboole_0
        | v1_funct_2(X43,X41,X42)
        | X41 = k1_xboole_0
        | X42 != k1_xboole_0
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_104,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | k1_relset_1(X38,X39,X40) = k1_relat_1(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_105,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_100,c_0_76])).

cnf(c_0_106,negated_conjecture,
    ( ~ v1_funct_2(esk5_0,k1_relat_1(esk5_0),k2_relat_1(esk5_0))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),k2_relat_1(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_102])])).

cnf(c_0_107,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_108,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_109,plain,
    ( k1_relat_1(X1) = k1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_52]),c_0_34])).

cnf(c_0_110,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_111,plain,
    ( k1_xboole_0 = X1
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_63]),c_0_26])])).

cnf(c_0_112,plain,
    ( v1_xboole_0(X1)
    | k6_relat_1(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_105,c_0_56])).

cnf(c_0_113,negated_conjecture,
    ( ~ v1_funct_2(esk5_0,k1_relat_1(esk5_0),k2_relat_1(esk5_0))
    | ~ r1_tarski(esk5_0,k2_zfmisc_1(k1_relat_1(esk5_0),k2_relat_1(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_106,c_0_28])).

cnf(c_0_114,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_28])).

cnf(c_0_115,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_28])).

cnf(c_0_116,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_53]),c_0_54]),c_0_26])])).

cnf(c_0_117,plain,
    ( k2_relat_1(X1) = k2_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_110]),c_0_34])).

cnf(c_0_118,plain,
    ( k1_xboole_0 = X1
    | k6_relat_1(k2_relat_1(X1)) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_119,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_xboole_0
    | ~ r1_tarski(esk5_0,k2_zfmisc_1(k1_relat_1(esk5_0),k2_relat_1(esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115])).

cnf(c_0_120,negated_conjecture,
    ( ~ v1_funct_2(esk5_0,k1_xboole_0,k2_relat_1(esk5_0))
    | ~ r1_tarski(esk5_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_116]),c_0_97])).

cnf(c_0_121,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_75]),c_0_54]),c_0_26])])).

cnf(c_0_122,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | k6_relat_1(k2_relat_1(esk5_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_118,c_0_44])).

cnf(c_0_123,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_50]),c_0_44])])).

cnf(c_0_124,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_87,c_0_76])).

cnf(c_0_125,negated_conjecture,
    ( ~ v1_funct_2(esk5_0,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_126,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_123]),c_0_124])])).

cnf(c_0_127,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_128,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_126]),c_0_126]),c_0_26])])).

cnf(c_0_129,plain,
    ( v1_funct_2(X1,X2,X3)
    | k1_relset_1(X2,X3,X1) != X2
    | X2 != k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_127,c_0_28])).

cnf(c_0_130,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_26]),c_0_53])).

cnf(c_0_131,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_130]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:43:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.39/0.55  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.39/0.55  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.39/0.55  #
% 0.39/0.55  # Preprocessing time       : 0.043 s
% 0.39/0.55  # Presaturation interreduction done
% 0.39/0.55  
% 0.39/0.55  # Proof found!
% 0.39/0.55  # SZS status Theorem
% 0.39/0.55  # SZS output start CNFRefutation
% 0.39/0.55  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.39/0.55  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.39/0.55  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.39/0.55  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.39/0.55  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.39/0.55  fof(t3_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.39/0.55  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.39/0.55  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.39/0.55  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.39/0.55  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 0.39/0.55  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.39/0.55  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.39/0.55  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.39/0.55  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.39/0.55  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.39/0.55  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.39/0.55  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.39/0.55  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.39/0.55  fof(c_0_18, plain, ![X33, X34]:(~r2_hidden(X33,X34)|~r1_tarski(X34,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.39/0.55  fof(c_0_19, plain, ![X17, X18, X19, X21, X22, X23, X24, X26]:(((~r2_hidden(X19,X18)|r2_hidden(k4_tarski(X19,esk2_3(X17,X18,X19)),X17)|X18!=k1_relat_1(X17))&(~r2_hidden(k4_tarski(X21,X22),X17)|r2_hidden(X21,X18)|X18!=k1_relat_1(X17)))&((~r2_hidden(esk3_2(X23,X24),X24)|~r2_hidden(k4_tarski(esk3_2(X23,X24),X26),X23)|X24=k1_relat_1(X23))&(r2_hidden(esk3_2(X23,X24),X24)|r2_hidden(k4_tarski(esk3_2(X23,X24),esk4_2(X23,X24)),X23)|X24=k1_relat_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.39/0.55  cnf(c_0_20, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.55  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.55  fof(c_0_22, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.39/0.55  fof(c_0_23, plain, ![X15, X16]:(~v1_relat_1(X15)|(~m1_subset_1(X16,k1_zfmisc_1(X15))|v1_relat_1(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.39/0.55  fof(c_0_24, plain, ![X13, X14]:((~m1_subset_1(X13,k1_zfmisc_1(X14))|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|m1_subset_1(X13,k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.39/0.55  cnf(c_0_25, plain, (X1!=k1_relat_1(X2)|~r1_tarski(X2,k4_tarski(X3,esk2_3(X2,X1,X3)))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.39/0.55  cnf(c_0_26, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.39/0.55  cnf(c_0_27, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.55  cnf(c_0_28, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.39/0.55  fof(c_0_29, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))))), inference(assume_negation,[status(cth)],[t3_funct_2])).
% 0.39/0.55  fof(c_0_30, plain, ![X35, X36, X37]:(~v1_xboole_0(X35)|(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X36,X35)))|v1_xboole_0(X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.39/0.55  fof(c_0_31, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.39/0.55  cnf(c_0_32, plain, (X1!=k1_relat_1(k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.39/0.55  fof(c_0_33, plain, ![X6]:(X6=k1_xboole_0|r2_hidden(esk1_1(X6),X6)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.39/0.55  cnf(c_0_34, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.39/0.55  fof(c_0_35, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&(~v1_funct_1(esk5_0)|~v1_funct_2(esk5_0,k1_relat_1(esk5_0),k2_relat_1(esk5_0))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),k2_relat_1(esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.39/0.55  cnf(c_0_36, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.39/0.55  cnf(c_0_37, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.39/0.55  fof(c_0_38, plain, ![X28]:(~v1_relat_1(X28)|r1_tarski(X28,k2_zfmisc_1(k1_relat_1(X28),k2_relat_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.39/0.55  fof(c_0_39, plain, ![X11, X12]:((k2_zfmisc_1(X11,X12)!=k1_xboole_0|(X11=k1_xboole_0|X12=k1_xboole_0))&((X11!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0)&(X12!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.39/0.55  fof(c_0_40, plain, ![X29, X30]:((r1_tarski(k1_relat_1(X29),k1_relat_1(X30))|~r1_tarski(X29,X30)|~v1_relat_1(X30)|~v1_relat_1(X29))&(r1_tarski(k2_relat_1(X29),k2_relat_1(X30))|~r1_tarski(X29,X30)|~v1_relat_1(X30)|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.39/0.55  cnf(c_0_41, plain, (~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(er,[status(thm)],[c_0_32])).
% 0.39/0.55  cnf(c_0_42, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.39/0.55  cnf(c_0_43, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_34, c_0_26])).
% 0.39/0.55  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.39/0.55  fof(c_0_45, plain, ![X31]:(k1_relat_1(k6_relat_1(X31))=X31&k2_relat_1(k6_relat_1(X31))=X31), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.39/0.55  fof(c_0_46, plain, ![X32]:(v1_relat_1(k6_relat_1(X32))&v1_funct_1(k6_relat_1(X32))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.39/0.55  fof(c_0_47, plain, ![X5]:(~v1_xboole_0(X5)|X5=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.39/0.55  cnf(c_0_48, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_36, c_0_28])).
% 0.39/0.55  cnf(c_0_49, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_37])).
% 0.39/0.55  cnf(c_0_50, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.39/0.55  cnf(c_0_51, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.39/0.55  cnf(c_0_52, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.39/0.55  cnf(c_0_53, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.39/0.55  cnf(c_0_54, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.39/0.55  cnf(c_0_55, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.39/0.55  cnf(c_0_56, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.39/0.55  cnf(c_0_57, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.39/0.55  cnf(c_0_58, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.39/0.55  cnf(c_0_59, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.39/0.55  cnf(c_0_60, plain, (r1_tarski(X1,k1_xboole_0)|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.39/0.55  cnf(c_0_61, plain, (r1_tarski(k1_relat_1(X1),k1_xboole_0)|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 0.39/0.55  cnf(c_0_62, plain, (r1_tarski(k6_relat_1(X1),k2_zfmisc_1(X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_55]), c_0_56]), c_0_57])])).
% 0.39/0.55  cnf(c_0_63, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.39/0.55  cnf(c_0_64, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.39/0.55  cnf(c_0_65, plain, (r1_tarski(k6_relat_1(X1),k1_xboole_0)|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_57]), c_0_55])).
% 0.39/0.55  cnf(c_0_66, plain, (r1_tarski(X1,k1_xboole_0)|~r1_tarski(k6_relat_1(X1),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_57]), c_0_56])).
% 0.39/0.55  cnf(c_0_67, plain, (r1_tarski(k6_relat_1(X1),k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.39/0.55  cnf(c_0_68, plain, (k6_relat_1(X1)=k1_xboole_0|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_26])])).
% 0.39/0.55  cnf(c_0_69, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_32, c_0_53])).
% 0.39/0.55  cnf(c_0_70, plain, (r1_tarski(X1,k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.39/0.55  cnf(c_0_71, plain, (k2_relat_1(k1_xboole_0)=X1|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_68])).
% 0.39/0.55  cnf(c_0_72, plain, (X1!=k1_relat_1(X2)|X2!=k1_xboole_0|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_69, c_0_21])).
% 0.39/0.55  cnf(c_0_73, plain, (k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))=X1|~v1_relat_1(X1)|~r1_tarski(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)),X1)), inference(spm,[status(thm)],[c_0_64, c_0_50])).
% 0.39/0.55  cnf(c_0_74, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_70, c_0_59])).
% 0.39/0.55  cnf(c_0_75, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_71])).
% 0.39/0.55  cnf(c_0_76, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.39/0.55  cnf(c_0_77, plain, (X1=k1_xboole_0|X1!=k1_relat_1(X2)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_42])).
% 0.39/0.55  cnf(c_0_78, plain, (r1_tarski(X1,k1_xboole_0)|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_68]), c_0_26])])).
% 0.39/0.55  cnf(c_0_79, plain, (X1!=k1_relat_1(X2)|X3!=k1_relat_1(X1)|X2!=k1_xboole_0|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_72, c_0_21])).
% 0.39/0.55  cnf(c_0_80, plain, (v1_xboole_0(k6_relat_1(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_48, c_0_62])).
% 0.39/0.55  cnf(c_0_81, plain, (k2_zfmisc_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_53]), c_0_75]), c_0_54]), c_0_75]), c_0_76])])).
% 0.39/0.55  cnf(c_0_82, plain, (v1_relat_1(k1_relat_1(X1))|~v1_relat_1(k1_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_52]), c_0_34])).
% 0.39/0.55  cnf(c_0_83, plain, (k1_relat_1(X1)=k1_xboole_0|X1!=k1_xboole_0), inference(er,[status(thm)],[c_0_77])).
% 0.39/0.55  cnf(c_0_84, plain, (v1_relat_1(X1)|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_78]), c_0_54])])).
% 0.39/0.55  cnf(c_0_85, plain, (X1=k1_xboole_0|X2!=k1_relat_1(X3)|X1!=k1_relat_1(X2)|X3!=k1_xboole_0), inference(spm,[status(thm)],[c_0_79, c_0_42])).
% 0.39/0.55  cnf(c_0_86, plain, (r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(X1,k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_56]), c_0_57])])).
% 0.39/0.55  cnf(c_0_87, plain, (k6_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_58, c_0_80])).
% 0.39/0.55  cnf(c_0_88, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_81]), c_0_76])])).
% 0.39/0.55  cnf(c_0_89, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.39/0.55  cnf(c_0_90, plain, (v1_relat_1(k1_relat_1(X1))|X2!=k1_xboole_0|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_54])]), c_0_84])).
% 0.39/0.55  cnf(c_0_91, plain, (X1=k1_xboole_0|X1!=k1_relat_1(k1_relat_1(X2))|X2!=k1_xboole_0), inference(er,[status(thm)],[c_0_85])).
% 0.39/0.55  cnf(c_0_92, plain, (r1_tarski(X1,X2)|~r1_tarski(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_57]), c_0_56])).
% 0.39/0.55  cnf(c_0_93, plain, (k6_relat_1(X1)=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.39/0.55  cnf(c_0_94, plain, (r1_tarski(X1,k1_xboole_0)|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_89])).
% 0.39/0.55  cnf(c_0_95, plain, (v1_relat_1(k1_relat_1(X1))|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_90, c_0_78])).
% 0.39/0.55  cnf(c_0_96, plain, (k1_relat_1(k1_relat_1(X1))=k1_xboole_0|X1!=k1_xboole_0), inference(er,[status(thm)],[c_0_91])).
% 0.39/0.55  cnf(c_0_97, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_26])])).
% 0.39/0.55  cnf(c_0_98, plain, (r1_tarski(k1_relat_1(X1),k1_xboole_0)|X1!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96])).
% 0.39/0.55  cnf(c_0_99, plain, (r1_tarski(k1_relat_1(X1),X2)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.39/0.55  cnf(c_0_100, plain, (v1_xboole_0(k1_relat_1(X1))|X1!=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_48, c_0_99])).
% 0.39/0.55  cnf(c_0_101, negated_conjecture, (~v1_funct_1(esk5_0)|~v1_funct_2(esk5_0,k1_relat_1(esk5_0),k2_relat_1(esk5_0))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),k2_relat_1(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.39/0.55  cnf(c_0_102, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.39/0.55  fof(c_0_103, plain, ![X41, X42, X43]:((((~v1_funct_2(X43,X41,X42)|X41=k1_relset_1(X41,X42,X43)|X42=k1_xboole_0|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))&(X41!=k1_relset_1(X41,X42,X43)|v1_funct_2(X43,X41,X42)|X42=k1_xboole_0|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))&((~v1_funct_2(X43,X41,X42)|X41=k1_relset_1(X41,X42,X43)|X41!=k1_xboole_0|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))&(X41!=k1_relset_1(X41,X42,X43)|v1_funct_2(X43,X41,X42)|X41!=k1_xboole_0|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))))&((~v1_funct_2(X43,X41,X42)|X43=k1_xboole_0|X41=k1_xboole_0|X42!=k1_xboole_0|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))&(X43!=k1_xboole_0|v1_funct_2(X43,X41,X42)|X41=k1_xboole_0|X42!=k1_xboole_0|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.39/0.55  fof(c_0_104, plain, ![X38, X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|k1_relset_1(X38,X39,X40)=k1_relat_1(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.39/0.55  cnf(c_0_105, plain, (v1_xboole_0(k1_relat_1(X1))|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_100, c_0_76])).
% 0.39/0.55  cnf(c_0_106, negated_conjecture, (~v1_funct_2(esk5_0,k1_relat_1(esk5_0),k2_relat_1(esk5_0))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),k2_relat_1(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_102])])).
% 0.39/0.55  cnf(c_0_107, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.39/0.55  cnf(c_0_108, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_104])).
% 0.39/0.55  cnf(c_0_109, plain, (k1_relat_1(X1)=k1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_52]), c_0_34])).
% 0.39/0.55  cnf(c_0_110, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.39/0.55  cnf(c_0_111, plain, (k1_xboole_0=X1|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_63]), c_0_26])])).
% 0.39/0.55  cnf(c_0_112, plain, (v1_xboole_0(X1)|k6_relat_1(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_105, c_0_56])).
% 0.39/0.55  cnf(c_0_113, negated_conjecture, (~v1_funct_2(esk5_0,k1_relat_1(esk5_0),k2_relat_1(esk5_0))|~r1_tarski(esk5_0,k2_zfmisc_1(k1_relat_1(esk5_0),k2_relat_1(esk5_0)))), inference(spm,[status(thm)],[c_0_106, c_0_28])).
% 0.39/0.55  cnf(c_0_114, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relset_1(X3,X1,X2)!=X3|~r1_tarski(X2,k2_zfmisc_1(X3,X1))), inference(spm,[status(thm)],[c_0_107, c_0_28])).
% 0.39/0.55  cnf(c_0_115, plain, (k1_relset_1(X1,X2,X3)=k1_relat_1(X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_108, c_0_28])).
% 0.39/0.55  cnf(c_0_116, plain, (k1_relat_1(X1)=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_53]), c_0_54]), c_0_26])])).
% 0.39/0.55  cnf(c_0_117, plain, (k2_relat_1(X1)=k2_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_110]), c_0_34])).
% 0.39/0.55  cnf(c_0_118, plain, (k1_xboole_0=X1|k6_relat_1(k2_relat_1(X1))!=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 0.39/0.55  cnf(c_0_119, negated_conjecture, (k2_relat_1(esk5_0)=k1_xboole_0|~r1_tarski(esk5_0,k2_zfmisc_1(k1_relat_1(esk5_0),k2_relat_1(esk5_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_115])).
% 0.39/0.55  cnf(c_0_120, negated_conjecture, (~v1_funct_2(esk5_0,k1_xboole_0,k2_relat_1(esk5_0))|~r1_tarski(esk5_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_116]), c_0_97])).
% 0.39/0.55  cnf(c_0_121, plain, (k2_relat_1(X1)=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_75]), c_0_54]), c_0_26])])).
% 0.39/0.55  cnf(c_0_122, negated_conjecture, (esk5_0=k1_xboole_0|k6_relat_1(k2_relat_1(esk5_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_118, c_0_44])).
% 0.39/0.55  cnf(c_0_123, negated_conjecture, (k2_relat_1(esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_50]), c_0_44])])).
% 0.39/0.55  cnf(c_0_124, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_87, c_0_76])).
% 0.39/0.55  cnf(c_0_125, negated_conjecture, (~v1_funct_2(esk5_0,k1_xboole_0,k1_xboole_0)|~r1_tarski(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_120, c_0_121])).
% 0.39/0.55  cnf(c_0_126, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122, c_0_123]), c_0_124])])).
% 0.39/0.55  cnf(c_0_127, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.39/0.55  cnf(c_0_128, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125, c_0_126]), c_0_126]), c_0_26])])).
% 0.39/0.55  cnf(c_0_129, plain, (v1_funct_2(X1,X2,X3)|k1_relset_1(X2,X3,X1)!=X2|X2!=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_127, c_0_28])).
% 0.39/0.55  cnf(c_0_130, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_26]), c_0_53])).
% 0.39/0.55  cnf(c_0_131, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_130]), c_0_26])]), ['proof']).
% 0.39/0.55  # SZS output end CNFRefutation
% 0.39/0.55  # Proof object total steps             : 132
% 0.39/0.55  # Proof object clause steps            : 96
% 0.39/0.55  # Proof object formula steps           : 36
% 0.39/0.55  # Proof object conjectures             : 17
% 0.39/0.55  # Proof object clause conjectures      : 14
% 0.39/0.55  # Proof object formula conjectures     : 3
% 0.39/0.55  # Proof object initial clauses used    : 25
% 0.39/0.55  # Proof object initial formulas used   : 18
% 0.39/0.55  # Proof object generating inferences   : 66
% 0.39/0.55  # Proof object simplifying inferences  : 60
% 0.39/0.55  # Training examples: 0 positive, 0 negative
% 0.39/0.55  # Parsed axioms                        : 18
% 0.39/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.55  # Initial clauses                      : 36
% 0.39/0.55  # Removed in clause preprocessing      : 0
% 0.39/0.55  # Initial clauses in saturation        : 36
% 0.39/0.55  # Processed clauses                    : 1597
% 0.39/0.55  # ...of these trivial                  : 17
% 0.39/0.55  # ...subsumed                          : 1000
% 0.39/0.55  # ...remaining for further processing  : 580
% 0.39/0.55  # Other redundant clauses eliminated   : 14
% 0.39/0.55  # Clauses deleted for lack of memory   : 0
% 0.39/0.55  # Backward-subsumed                    : 103
% 0.39/0.55  # Backward-rewritten                   : 52
% 0.39/0.55  # Generated clauses                    : 14675
% 0.39/0.55  # ...of the previous two non-trivial   : 9358
% 0.39/0.55  # Contextual simplify-reflections      : 54
% 0.39/0.55  # Paramodulations                      : 14610
% 0.39/0.55  # Factorizations                       : 0
% 0.39/0.55  # Equation resolutions                 : 65
% 0.39/0.55  # Propositional unsat checks           : 0
% 0.39/0.55  #    Propositional check models        : 0
% 0.39/0.55  #    Propositional check unsatisfiable : 0
% 0.39/0.55  #    Propositional clauses             : 0
% 0.39/0.55  #    Propositional clauses after purity: 0
% 0.39/0.55  #    Propositional unsat core size     : 0
% 0.39/0.55  #    Propositional preprocessing time  : 0.000
% 0.39/0.55  #    Propositional encoding time       : 0.000
% 0.39/0.55  #    Propositional solver time         : 0.000
% 0.39/0.55  #    Success case prop preproc time    : 0.000
% 0.39/0.55  #    Success case prop encoding time   : 0.000
% 0.39/0.55  #    Success case prop solver time     : 0.000
% 0.39/0.55  # Current number of processed clauses  : 388
% 0.39/0.55  #    Positive orientable unit clauses  : 17
% 0.39/0.55  #    Positive unorientable unit clauses: 1
% 0.39/0.56  #    Negative unit clauses             : 2
% 0.39/0.56  #    Non-unit-clauses                  : 368
% 0.39/0.56  # Current number of unprocessed clauses: 7667
% 0.39/0.56  # ...number of literals in the above   : 27491
% 0.39/0.56  # Current number of archived formulas  : 0
% 0.39/0.56  # Current number of archived clauses   : 190
% 0.39/0.56  # Clause-clause subsumption calls (NU) : 36970
% 0.39/0.56  # Rec. Clause-clause subsumption calls : 30025
% 0.39/0.56  # Non-unit clause-clause subsumptions  : 1152
% 0.39/0.56  # Unit Clause-clause subsumption calls : 282
% 0.39/0.56  # Rewrite failures with RHS unbound    : 0
% 0.39/0.56  # BW rewrite match attempts            : 32
% 0.39/0.56  # BW rewrite match successes           : 7
% 0.39/0.56  # Condensation attempts                : 0
% 0.39/0.56  # Condensation successes               : 0
% 0.39/0.56  # Termbank termtop insertions          : 147988
% 0.39/0.56  
% 0.39/0.56  # -------------------------------------------------
% 0.39/0.56  # User time                : 0.200 s
% 0.39/0.56  # System time              : 0.011 s
% 0.39/0.56  # Total time               : 0.212 s
% 0.39/0.56  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
