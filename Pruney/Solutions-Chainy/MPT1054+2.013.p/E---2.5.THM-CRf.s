%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:18 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 117 expanded)
%              Number of clauses        :   39 (  52 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  164 ( 259 expanded)
%              Number of equality atoms :   50 (  69 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t171_funct_2,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t217_relat_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v4_relat_1(X3,X1) )
         => v4_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

fof(fc24_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v4_relat_1(k6_relat_1(X1),X1)
      & v5_relat_1(k6_relat_1(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(t155_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => k10_relat_1(X2,X1) = k9_relat_1(k2_funct_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(t67_funct_1,axiom,(
    ! [X1] : k2_funct_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(t181_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k10_relat_1(k5_relat_1(X2,X3),X1) = k10_relat_1(X2,k10_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t171_funct_2])).

fof(c_0_19,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | r1_tarski(X7,X5)
        | X6 != k1_zfmisc_1(X5) )
      & ( ~ r1_tarski(X8,X5)
        | r2_hidden(X8,X6)
        | X6 != k1_zfmisc_1(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | ~ r1_tarski(esk1_2(X9,X10),X9)
        | X10 = k1_zfmisc_1(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(esk1_2(X9,X10),X9)
        | X10 = k1_zfmisc_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_20,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X13,X14)
      | v1_xboole_0(X14)
      | r2_hidden(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & k8_relset_1(esk2_0,esk2_0,k6_partfun1(esk2_0),esk3_0) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_22,plain,(
    ! [X12] : ~ v1_xboole_0(k1_zfmisc_1(X12)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_23,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_tarski(X22,X23)
      | ~ v1_relat_1(X24)
      | ~ v4_relat_1(X24,X22)
      | v4_relat_1(X24,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t217_relat_1])])])).

fof(c_0_24,plain,(
    ! [X28] :
      ( v1_relat_1(k6_relat_1(X28))
      & v4_relat_1(k6_relat_1(X28),X28)
      & v5_relat_1(k6_relat_1(X28),X28) ) ),
    inference(variable_rename,[status(thm)],[fc24_relat_1])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | ~ v1_funct_1(X32)
      | ~ v2_funct_1(X32)
      | k10_relat_1(X32,X31) = k9_relat_1(k2_funct_1(X32),X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).

fof(c_0_30,plain,(
    ! [X33] : k2_funct_1(k6_relat_1(X33)) = k6_relat_1(X33) ),
    inference(variable_rename,[status(thm)],[t67_funct_1])).

fof(c_0_31,plain,(
    ! [X30] :
      ( v1_relat_1(k6_relat_1(X30))
      & v2_funct_1(k6_relat_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_32,plain,(
    ! [X29] :
      ( v1_relat_1(k6_relat_1(X29))
      & v1_funct_1(k6_relat_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_33,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k2_relat_1(k7_relat_1(X16,X15)) = k9_relat_1(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_34,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ v4_relat_1(X21,X20)
      | X21 = k7_relat_1(X21,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_35,plain,
    ( v4_relat_1(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v4_relat_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

fof(c_0_39,plain,(
    ! [X38] :
      ( v1_partfun1(k6_partfun1(X38),X38)
      & m1_subset_1(k6_partfun1(X38),k1_zfmisc_1(k2_zfmisc_1(X38,X38))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_40,plain,(
    ! [X39] : k6_partfun1(X39) = k6_relat_1(X39) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_41,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | ~ r1_tarski(k1_relat_1(X27),X26)
      | k5_relat_1(k6_relat_1(X26),X27) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

fof(c_0_42,plain,(
    ! [X25] :
      ( k1_relat_1(k6_relat_1(X25)) = X25
      & k2_relat_1(k6_relat_1(X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_43,plain,
    ( k10_relat_1(X1,X2) = k9_relat_1(k2_funct_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( k2_funct_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,plain,
    ( v4_relat_1(k6_relat_1(X1),X2)
    | ~ v4_relat_1(k6_relat_1(X1),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_51,plain,(
    ! [X34,X35,X36,X37] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k8_relset_1(X34,X35,X36,X37) = k10_relat_1(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_52,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_54,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | k10_relat_1(k5_relat_1(X18,X19),X17) = k10_relat_1(X18,k10_relat_1(X19,X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t181_relat_1])])])).

cnf(c_0_55,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,plain,
    ( k9_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46]),c_0_36])])).

cnf(c_0_58,plain,
    ( k9_relat_1(X1,X2) = k2_relat_1(X1)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_60,negated_conjecture,
    ( v4_relat_1(k6_relat_1(X1),esk2_0)
    | ~ v4_relat_1(k6_relat_1(X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_61,plain,
    ( v4_relat_1(k6_relat_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_62,negated_conjecture,
    ( k8_relset_1(esk2_0,esk2_0,k6_partfun1(esk2_0),esk3_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_63,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_64,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_65,plain,
    ( k10_relat_1(k5_relat_1(X1,X2),X3) = k10_relat_1(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_66,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_36])])).

cnf(c_0_67,plain,
    ( k10_relat_1(k6_relat_1(X1),X2) = X1
    | ~ v4_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_36])])).

cnf(c_0_68,negated_conjecture,
    ( v4_relat_1(k6_relat_1(esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( k8_relset_1(esk2_0,esk2_0,k6_relat_1(esk2_0),esk3_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_62,c_0_53])).

cnf(c_0_70,plain,
    ( k8_relset_1(X1,X1,k6_relat_1(X1),X2) = k10_relat_1(k6_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,plain,
    ( k10_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X2),X3)) = k10_relat_1(k6_relat_1(X2),X3)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_36]),c_0_36])])).

cnf(c_0_72,negated_conjecture,
    ( k10_relat_1(k6_relat_1(esk3_0),esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( k10_relat_1(k6_relat_1(esk2_0),esk3_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( k10_relat_1(k6_relat_1(X1),esk3_0) = esk3_0
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:14:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05BN
% 0.12/0.36  # and selection function SelectUnlessUniqMaxSmallestOrientable.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.022 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t171_funct_2, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k8_relset_1(X1,X1,k6_partfun1(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 0.12/0.36  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.12/0.36  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.12/0.36  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.12/0.36  fof(t217_relat_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>![X3]:((v1_relat_1(X3)&v4_relat_1(X3,X1))=>v4_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t217_relat_1)).
% 0.12/0.36  fof(fc24_relat_1, axiom, ![X1]:((v1_relat_1(k6_relat_1(X1))&v4_relat_1(k6_relat_1(X1),X1))&v5_relat_1(k6_relat_1(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 0.12/0.36  fof(t155_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>k10_relat_1(X2,X1)=k9_relat_1(k2_funct_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 0.12/0.36  fof(t67_funct_1, axiom, ![X1]:k2_funct_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 0.12/0.36  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.12/0.36  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.12/0.36  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.12/0.36  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.12/0.36  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.12/0.36  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.12/0.36  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 0.12/0.36  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.12/0.36  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.12/0.36  fof(t181_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k10_relat_1(k5_relat_1(X2,X3),X1)=k10_relat_1(X2,k10_relat_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 0.12/0.36  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k8_relset_1(X1,X1,k6_partfun1(X1),X2)=X2)), inference(assume_negation,[status(cth)],[t171_funct_2])).
% 0.12/0.36  fof(c_0_19, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|r1_tarski(X7,X5)|X6!=k1_zfmisc_1(X5))&(~r1_tarski(X8,X5)|r2_hidden(X8,X6)|X6!=k1_zfmisc_1(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|~r1_tarski(esk1_2(X9,X10),X9)|X10=k1_zfmisc_1(X9))&(r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(esk1_2(X9,X10),X9)|X10=k1_zfmisc_1(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.12/0.36  fof(c_0_20, plain, ![X13, X14]:(~m1_subset_1(X13,X14)|(v1_xboole_0(X14)|r2_hidden(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.12/0.36  fof(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&k8_relset_1(esk2_0,esk2_0,k6_partfun1(esk2_0),esk3_0)!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.12/0.36  fof(c_0_22, plain, ![X12]:~v1_xboole_0(k1_zfmisc_1(X12)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.12/0.36  fof(c_0_23, plain, ![X22, X23, X24]:(~r1_tarski(X22,X23)|(~v1_relat_1(X24)|~v4_relat_1(X24,X22)|v4_relat_1(X24,X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t217_relat_1])])])).
% 0.12/0.36  fof(c_0_24, plain, ![X28]:((v1_relat_1(k6_relat_1(X28))&v4_relat_1(k6_relat_1(X28),X28))&v5_relat_1(k6_relat_1(X28),X28)), inference(variable_rename,[status(thm)],[fc24_relat_1])).
% 0.12/0.36  cnf(c_0_25, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.36  cnf(c_0_26, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.36  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.36  cnf(c_0_28, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.36  fof(c_0_29, plain, ![X31, X32]:(~v1_relat_1(X32)|~v1_funct_1(X32)|(~v2_funct_1(X32)|k10_relat_1(X32,X31)=k9_relat_1(k2_funct_1(X32),X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).
% 0.12/0.36  fof(c_0_30, plain, ![X33]:k2_funct_1(k6_relat_1(X33))=k6_relat_1(X33), inference(variable_rename,[status(thm)],[t67_funct_1])).
% 0.12/0.36  fof(c_0_31, plain, ![X30]:(v1_relat_1(k6_relat_1(X30))&v2_funct_1(k6_relat_1(X30))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.12/0.36  fof(c_0_32, plain, ![X29]:(v1_relat_1(k6_relat_1(X29))&v1_funct_1(k6_relat_1(X29))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.12/0.36  fof(c_0_33, plain, ![X15, X16]:(~v1_relat_1(X16)|k2_relat_1(k7_relat_1(X16,X15))=k9_relat_1(X16,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.12/0.36  fof(c_0_34, plain, ![X20, X21]:(~v1_relat_1(X21)|~v4_relat_1(X21,X20)|X21=k7_relat_1(X21,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.12/0.36  cnf(c_0_35, plain, (v4_relat_1(X3,X2)|~r1_tarski(X1,X2)|~v1_relat_1(X3)|~v4_relat_1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.36  cnf(c_0_36, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.36  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_25])).
% 0.12/0.36  cnf(c_0_38, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.12/0.36  fof(c_0_39, plain, ![X38]:(v1_partfun1(k6_partfun1(X38),X38)&m1_subset_1(k6_partfun1(X38),k1_zfmisc_1(k2_zfmisc_1(X38,X38)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.12/0.36  fof(c_0_40, plain, ![X39]:k6_partfun1(X39)=k6_relat_1(X39), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.12/0.36  fof(c_0_41, plain, ![X26, X27]:(~v1_relat_1(X27)|(~r1_tarski(k1_relat_1(X27),X26)|k5_relat_1(k6_relat_1(X26),X27)=X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.12/0.36  fof(c_0_42, plain, ![X25]:(k1_relat_1(k6_relat_1(X25))=X25&k2_relat_1(k6_relat_1(X25))=X25), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.12/0.36  cnf(c_0_43, plain, (k10_relat_1(X1,X2)=k9_relat_1(k2_funct_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.36  cnf(c_0_44, plain, (k2_funct_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.36  cnf(c_0_45, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.36  cnf(c_0_46, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.36  cnf(c_0_47, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.36  cnf(c_0_48, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.36  cnf(c_0_49, plain, (v4_relat_1(k6_relat_1(X1),X2)|~v4_relat_1(k6_relat_1(X1),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.36  cnf(c_0_50, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.36  fof(c_0_51, plain, ![X34, X35, X36, X37]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k8_relset_1(X34,X35,X36,X37)=k10_relat_1(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.12/0.36  cnf(c_0_52, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.36  cnf(c_0_53, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.36  fof(c_0_54, plain, ![X17, X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|k10_relat_1(k5_relat_1(X18,X19),X17)=k10_relat_1(X18,k10_relat_1(X19,X17)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t181_relat_1])])])).
% 0.12/0.36  cnf(c_0_55, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.12/0.36  cnf(c_0_56, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.12/0.36  cnf(c_0_57, plain, (k9_relat_1(k6_relat_1(X1),X2)=k10_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46]), c_0_36])])).
% 0.12/0.36  cnf(c_0_58, plain, (k9_relat_1(X1,X2)=k2_relat_1(X1)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.12/0.36  cnf(c_0_59, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.12/0.36  cnf(c_0_60, negated_conjecture, (v4_relat_1(k6_relat_1(X1),esk2_0)|~v4_relat_1(k6_relat_1(X1),esk3_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.12/0.36  cnf(c_0_61, plain, (v4_relat_1(k6_relat_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.36  cnf(c_0_62, negated_conjecture, (k8_relset_1(esk2_0,esk2_0,k6_partfun1(esk2_0),esk3_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.36  cnf(c_0_63, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.12/0.36  cnf(c_0_64, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_52, c_0_53])).
% 0.12/0.36  cnf(c_0_65, plain, (k10_relat_1(k5_relat_1(X1,X2),X3)=k10_relat_1(X1,k10_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.12/0.36  cnf(c_0_66, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_36])])).
% 0.12/0.36  cnf(c_0_67, plain, (k10_relat_1(k6_relat_1(X1),X2)=X1|~v4_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_36])])).
% 0.12/0.36  cnf(c_0_68, negated_conjecture, (v4_relat_1(k6_relat_1(esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.12/0.36  cnf(c_0_69, negated_conjecture, (k8_relset_1(esk2_0,esk2_0,k6_relat_1(esk2_0),esk3_0)!=esk3_0), inference(rw,[status(thm)],[c_0_62, c_0_53])).
% 0.12/0.36  cnf(c_0_70, plain, (k8_relset_1(X1,X1,k6_relat_1(X1),X2)=k10_relat_1(k6_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.12/0.36  cnf(c_0_71, plain, (k10_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X2),X3))=k10_relat_1(k6_relat_1(X2),X3)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_36]), c_0_36])])).
% 0.12/0.36  cnf(c_0_72, negated_conjecture, (k10_relat_1(k6_relat_1(esk3_0),esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.12/0.36  cnf(c_0_73, negated_conjecture, (k10_relat_1(k6_relat_1(esk2_0),esk3_0)!=esk3_0), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.12/0.36  cnf(c_0_74, negated_conjecture, (k10_relat_1(k6_relat_1(X1),esk3_0)=esk3_0|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.12/0.36  cnf(c_0_75, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_50])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 76
% 0.12/0.36  # Proof object clause steps            : 39
% 0.12/0.36  # Proof object formula steps           : 37
% 0.12/0.36  # Proof object conjectures             : 14
% 0.12/0.36  # Proof object clause conjectures      : 11
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 21
% 0.12/0.36  # Proof object initial formulas used   : 18
% 0.12/0.36  # Proof object generating inferences   : 14
% 0.12/0.36  # Proof object simplifying inferences  : 19
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 18
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 28
% 0.12/0.36  # Removed in clause preprocessing      : 1
% 0.12/0.36  # Initial clauses in saturation        : 27
% 0.12/0.36  # Processed clauses                    : 73
% 0.12/0.36  # ...of these trivial                  : 2
% 0.12/0.36  # ...subsumed                          : 0
% 0.12/0.36  # ...remaining for further processing  : 71
% 0.12/0.36  # Other redundant clauses eliminated   : 2
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 1
% 0.12/0.36  # Generated clauses                    : 30
% 0.12/0.36  # ...of the previous two non-trivial   : 28
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 28
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 2
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 43
% 0.12/0.36  #    Positive orientable unit clauses  : 20
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 2
% 0.12/0.36  #    Non-unit-clauses                  : 21
% 0.12/0.36  # Current number of unprocessed clauses: 6
% 0.12/0.36  # ...number of literals in the above   : 21
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 27
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 8
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 8
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.36  # Unit Clause-clause subsumption calls : 1
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 4
% 0.12/0.36  # BW rewrite match successes           : 1
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 2218
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.024 s
% 0.12/0.36  # System time              : 0.004 s
% 0.12/0.36  # Total time               : 0.028 s
% 0.12/0.36  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
