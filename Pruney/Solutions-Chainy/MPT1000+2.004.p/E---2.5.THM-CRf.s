%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 429 expanded)
%              Number of clauses        :   62 ( 183 expanded)
%              Number of leaves         :   20 ( 109 expanded)
%              Depth                    :   11
%              Number of atoms          :  279 (1535 expanded)
%              Number of equality atoms :  103 ( 571 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => k8_relset_1(X1,X2,X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(fc10_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => k8_relset_1(X1,X2,X3,X2) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t48_funct_2])).

fof(c_0_21,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_22,plain,(
    ! [X24,X25] :
      ( ( ~ v5_relat_1(X25,X24)
        | r1_tarski(k2_relat_1(X25),X24)
        | ~ v1_relat_1(X25) )
      & ( ~ r1_tarski(k2_relat_1(X25),X24)
        | v5_relat_1(X25,X24)
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_23,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_24,plain,(
    ! [X45,X46,X47] :
      ( ( ~ v1_funct_2(X47,X45,X46)
        | X45 = k1_relset_1(X45,X46,X47)
        | X46 = k1_xboole_0
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( X45 != k1_relset_1(X45,X46,X47)
        | v1_funct_2(X47,X45,X46)
        | X46 = k1_xboole_0
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( ~ v1_funct_2(X47,X45,X46)
        | X45 = k1_relset_1(X45,X46,X47)
        | X45 != k1_xboole_0
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( X45 != k1_relset_1(X45,X46,X47)
        | v1_funct_2(X47,X45,X46)
        | X45 != k1_xboole_0
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( ~ v1_funct_2(X47,X45,X46)
        | X47 = k1_xboole_0
        | X45 = k1_xboole_0
        | X46 != k1_xboole_0
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( X47 != k1_xboole_0
        | v1_funct_2(X47,X45,X46)
        | X45 = k1_xboole_0
        | X46 != k1_xboole_0
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_25,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & ( esk4_0 != k1_xboole_0
      | esk3_0 = k1_xboole_0 )
    & k8_relset_1(esk3_0,esk4_0,esk5_0,esk4_0) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_26,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X35,X36,X37] :
      ( ( v4_relat_1(X37,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( v5_relat_1(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_30,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | v1_relat_1(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_31,plain,(
    ! [X28,X29] : v1_relat_1(k2_zfmisc_1(X28,X29)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_34,plain,(
    ! [X27] :
      ( ~ v1_xboole_0(X27)
      | v1_xboole_0(k1_relat_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).

fof(c_0_35,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | k1_relset_1(X38,X39,X40) = k1_relat_1(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_36,plain,(
    ! [X15] :
      ( ~ v1_xboole_0(X15)
      | X15 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_37,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_40,plain,(
    ! [X18,X19] :
      ( ( k2_zfmisc_1(X18,X19) != k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_42,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X30)
      | ~ v1_relat_1(X31)
      | k1_relat_1(k5_relat_1(X30,X31)) = k10_relat_1(X30,k1_relat_1(X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_43,plain,(
    ! [X32] :
      ( k1_relat_1(k6_relat_1(X32)) = X32
      & k2_relat_1(k6_relat_1(X32)) = X32 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_44,plain,(
    ! [X26] : v1_relat_1(k6_relat_1(X26)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ v5_relat_1(X3,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k2_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_46,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_47,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_48,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_49,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_51,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_52,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_53,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_55,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk5_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_56,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_38])).

cnf(c_0_58,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_59,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_60,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_61,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X34)
      | ~ r1_tarski(k2_relat_1(X34),X33)
      | k5_relat_1(X34,k6_relat_1(X33)) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

cnf(c_0_62,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | r2_hidden(esk2_2(k2_relat_1(X1),X2),X3)
    | ~ v5_relat_1(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_33])).

cnf(c_0_63,negated_conjecture,
    ( v5_relat_1(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_38])).

cnf(c_0_64,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_38]),c_0_48])])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_66,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_67,plain,
    ( X1 = k1_relat_1(X2)
    | X1 != k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_68,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_51])).

cnf(c_0_69,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_55]),c_0_38])])).

cnf(c_0_70,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))
    | esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_56])).

cnf(c_0_72,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_57])).

fof(c_0_74,plain,(
    ! [X41,X42,X43,X44] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k8_relset_1(X41,X42,X43,X44) = k10_relat_1(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_75,plain,
    ( k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])])).

cnf(c_0_76,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk5_0),X1)
    | r2_hidden(esk2_2(k2_relat_1(esk5_0),X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

cnf(c_0_79,plain,
    ( X1 = k1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_80,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_38]),c_0_39])])).

cnf(c_0_81,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_xboole_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(esk5_0,k1_xboole_0)
    | esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_71])).

cnf(c_0_83,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_72])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_73])).

cnf(c_0_85,negated_conjecture,
    ( k8_relset_1(esk3_0,esk4_0,esk5_0,esk4_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_86,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_87,plain,
    ( k10_relat_1(X1,X2) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_89,negated_conjecture,
    ( X1 = esk3_0
    | ~ r1_tarski(X1,esk3_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_82]),c_0_83])])).

cnf(c_0_91,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_56]),c_0_72])])).

cnf(c_0_92,negated_conjecture,
    ( k10_relat_1(esk5_0,esk4_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_38])])).

cnf(c_0_93,negated_conjecture,
    ( k10_relat_1(esk5_0,esk4_0) = k1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_64])])).

cnf(c_0_94,negated_conjecture,
    ( X1 = esk3_0
    | esk4_0 != k1_xboole_0
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_72])])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_33])).

cnf(c_0_96,negated_conjecture,
    ( k1_relat_1(esk5_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( esk5_0 = esk3_0
    | esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_69,c_0_96])).

cnf(c_0_99,negated_conjecture,
    ( esk5_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98])])).

cnf(c_0_100,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_96,c_0_80])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_98])]),c_0_99]),c_0_100]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.44  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.20/0.44  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.44  #
% 0.20/0.44  # Preprocessing time       : 0.031 s
% 0.20/0.44  
% 0.20/0.44  # Proof found!
% 0.20/0.44  # SZS status Theorem
% 0.20/0.44  # SZS output start CNFRefutation
% 0.20/0.44  fof(t48_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>k8_relset_1(X1,X2,X3,X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 0.20/0.44  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.44  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.20/0.44  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.44  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.44  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.44  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.44  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.44  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.44  fof(fc10_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_xboole_0(k1_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 0.20/0.44  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.44  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.44  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.44  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.20/0.44  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.44  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.20/0.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.44  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 0.20/0.44  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.44  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.20/0.44  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>k8_relset_1(X1,X2,X3,X2)=X1))), inference(assume_negation,[status(cth)],[t48_funct_2])).
% 0.20/0.44  fof(c_0_21, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.44  fof(c_0_22, plain, ![X24, X25]:((~v5_relat_1(X25,X24)|r1_tarski(k2_relat_1(X25),X24)|~v1_relat_1(X25))&(~r1_tarski(k2_relat_1(X25),X24)|v5_relat_1(X25,X24)|~v1_relat_1(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.20/0.44  fof(c_0_23, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.44  fof(c_0_24, plain, ![X45, X46, X47]:((((~v1_funct_2(X47,X45,X46)|X45=k1_relset_1(X45,X46,X47)|X46=k1_xboole_0|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))&(X45!=k1_relset_1(X45,X46,X47)|v1_funct_2(X47,X45,X46)|X46=k1_xboole_0|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))))&((~v1_funct_2(X47,X45,X46)|X45=k1_relset_1(X45,X46,X47)|X45!=k1_xboole_0|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))&(X45!=k1_relset_1(X45,X46,X47)|v1_funct_2(X47,X45,X46)|X45!=k1_xboole_0|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))))&((~v1_funct_2(X47,X45,X46)|X47=k1_xboole_0|X45=k1_xboole_0|X46!=k1_xboole_0|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))&(X47!=k1_xboole_0|v1_funct_2(X47,X45,X46)|X45=k1_xboole_0|X46!=k1_xboole_0|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.44  fof(c_0_25, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&((esk4_0!=k1_xboole_0|esk3_0=k1_xboole_0)&k8_relset_1(esk3_0,esk4_0,esk5_0,esk4_0)!=esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.20/0.44  fof(c_0_26, plain, ![X20, X21]:((~m1_subset_1(X20,k1_zfmisc_1(X21))|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|m1_subset_1(X20,k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.44  cnf(c_0_27, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.44  cnf(c_0_28, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.44  fof(c_0_29, plain, ![X35, X36, X37]:((v4_relat_1(X37,X35)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(v5_relat_1(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.44  fof(c_0_30, plain, ![X22, X23]:(~v1_relat_1(X22)|(~m1_subset_1(X23,k1_zfmisc_1(X22))|v1_relat_1(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.44  fof(c_0_31, plain, ![X28, X29]:v1_relat_1(k2_zfmisc_1(X28,X29)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.44  cnf(c_0_32, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.44  cnf(c_0_33, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.44  fof(c_0_34, plain, ![X27]:(~v1_xboole_0(X27)|v1_xboole_0(k1_relat_1(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).
% 0.20/0.44  fof(c_0_35, plain, ![X38, X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|k1_relset_1(X38,X39,X40)=k1_relat_1(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.44  fof(c_0_36, plain, ![X15]:(~v1_xboole_0(X15)|X15=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.44  cnf(c_0_37, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.44  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.44  cnf(c_0_39, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.44  fof(c_0_40, plain, ![X18, X19]:((k2_zfmisc_1(X18,X19)!=k1_xboole_0|(X18=k1_xboole_0|X19=k1_xboole_0))&((X18!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0)&(X19!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.44  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.44  fof(c_0_42, plain, ![X30, X31]:(~v1_relat_1(X30)|(~v1_relat_1(X31)|k1_relat_1(k5_relat_1(X30,X31))=k10_relat_1(X30,k1_relat_1(X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.20/0.44  fof(c_0_43, plain, ![X32]:(k1_relat_1(k6_relat_1(X32))=X32&k2_relat_1(k6_relat_1(X32))=X32), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.44  fof(c_0_44, plain, ![X26]:v1_relat_1(k6_relat_1(X26)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.20/0.44  cnf(c_0_45, plain, (r2_hidden(X1,X2)|~v5_relat_1(X3,X2)|~v1_relat_1(X3)|~r2_hidden(X1,k2_relat_1(X3))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.44  cnf(c_0_46, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.44  cnf(c_0_47, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.44  cnf(c_0_48, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.44  fof(c_0_49, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.44  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.44  cnf(c_0_51, plain, (v1_xboole_0(k1_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.44  cnf(c_0_52, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.44  cnf(c_0_53, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.44  cnf(c_0_54, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.44  cnf(c_0_55, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk5_0)=esk3_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.20/0.44  cnf(c_0_56, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.44  cnf(c_0_57, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_41, c_0_38])).
% 0.20/0.44  cnf(c_0_58, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.44  cnf(c_0_59, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.44  cnf(c_0_60, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.44  fof(c_0_61, plain, ![X33, X34]:(~v1_relat_1(X34)|(~r1_tarski(k2_relat_1(X34),X33)|k5_relat_1(X34,k6_relat_1(X33))=X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 0.20/0.44  cnf(c_0_62, plain, (r1_tarski(k2_relat_1(X1),X2)|r2_hidden(esk2_2(k2_relat_1(X1),X2),X3)|~v5_relat_1(X1,X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_33])).
% 0.20/0.44  cnf(c_0_63, negated_conjecture, (v5_relat_1(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_38])).
% 0.20/0.44  cnf(c_0_64, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_38]), c_0_48])])).
% 0.20/0.44  cnf(c_0_65, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.44  cnf(c_0_66, plain, (r1_tarski(k1_relat_1(X1),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.44  cnf(c_0_67, plain, (X1=k1_relat_1(X2)|X1!=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.44  cnf(c_0_68, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_54, c_0_51])).
% 0.20/0.44  cnf(c_0_69, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_55]), c_0_38])])).
% 0.20/0.44  cnf(c_0_70, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.44  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))|esk4_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_56])).
% 0.20/0.44  cnf(c_0_72, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.44  cnf(c_0_73, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk3_0,esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_57])).
% 0.20/0.44  fof(c_0_74, plain, ![X41, X42, X43, X44]:(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|k8_relset_1(X41,X42,X43,X44)=k10_relat_1(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.20/0.44  cnf(c_0_75, plain, (k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])])).
% 0.20/0.44  cnf(c_0_76, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.44  cnf(c_0_77, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.44  cnf(c_0_78, negated_conjecture, (r1_tarski(k2_relat_1(esk5_0),X1)|r2_hidden(esk2_2(k2_relat_1(esk5_0),X1),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])])).
% 0.20/0.44  cnf(c_0_79, plain, (X1=k1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.44  cnf(c_0_80, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_38]), c_0_39])])).
% 0.20/0.44  cnf(c_0_81, negated_conjecture, (esk3_0=k1_xboole_0|~v1_xboole_0(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 0.20/0.44  cnf(c_0_82, negated_conjecture, (r1_tarski(esk5_0,k1_xboole_0)|esk4_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_71])).
% 0.20/0.44  cnf(c_0_83, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_50, c_0_72])).
% 0.20/0.44  cnf(c_0_84, negated_conjecture, (~r2_hidden(X1,esk5_0)|~v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_32, c_0_73])).
% 0.20/0.44  cnf(c_0_85, negated_conjecture, (k8_relset_1(esk3_0,esk4_0,esk5_0,esk4_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.44  cnf(c_0_86, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.44  cnf(c_0_87, plain, (k10_relat_1(X1,X2)=k1_relat_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.44  cnf(c_0_88, negated_conjecture, (r1_tarski(k2_relat_1(esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.44  cnf(c_0_89, negated_conjecture, (X1=esk3_0|~r1_tarski(X1,esk3_0)|~v1_xboole_0(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.20/0.44  cnf(c_0_90, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_82]), c_0_83])])).
% 0.20/0.44  cnf(c_0_91, negated_conjecture, (esk4_0!=k1_xboole_0|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_56]), c_0_72])])).
% 0.20/0.44  cnf(c_0_92, negated_conjecture, (k10_relat_1(esk5_0,esk4_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_38])])).
% 0.20/0.44  cnf(c_0_93, negated_conjecture, (k10_relat_1(esk5_0,esk4_0)=k1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_64])])).
% 0.20/0.44  cnf(c_0_94, negated_conjecture, (X1=esk3_0|esk4_0!=k1_xboole_0|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_72])])).
% 0.20/0.44  cnf(c_0_95, negated_conjecture, (r1_tarski(esk5_0,X1)|esk4_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_91, c_0_33])).
% 0.20/0.44  cnf(c_0_96, negated_conjecture, (k1_relat_1(esk5_0)!=esk3_0), inference(rw,[status(thm)],[c_0_92, c_0_93])).
% 0.20/0.44  cnf(c_0_97, negated_conjecture, (esk5_0=esk3_0|esk4_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.20/0.44  cnf(c_0_98, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_69, c_0_96])).
% 0.20/0.44  cnf(c_0_99, negated_conjecture, (esk5_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_98])])).
% 0.20/0.44  cnf(c_0_100, negated_conjecture, (esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_96, c_0_80])).
% 0.20/0.44  cnf(c_0_101, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_98])]), c_0_99]), c_0_100]), ['proof']).
% 0.20/0.44  # SZS output end CNFRefutation
% 0.20/0.44  # Proof object total steps             : 102
% 0.20/0.44  # Proof object clause steps            : 62
% 0.20/0.44  # Proof object formula steps           : 40
% 0.20/0.44  # Proof object conjectures             : 33
% 0.20/0.44  # Proof object clause conjectures      : 30
% 0.20/0.44  # Proof object formula conjectures     : 3
% 0.20/0.44  # Proof object initial clauses used    : 26
% 0.20/0.44  # Proof object initial formulas used   : 20
% 0.20/0.44  # Proof object generating inferences   : 32
% 0.20/0.44  # Proof object simplifying inferences  : 32
% 0.20/0.44  # Training examples: 0 positive, 0 negative
% 0.20/0.44  # Parsed axioms                        : 20
% 0.20/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.44  # Initial clauses                      : 40
% 0.20/0.44  # Removed in clause preprocessing      : 0
% 0.20/0.44  # Initial clauses in saturation        : 40
% 0.20/0.44  # Processed clauses                    : 795
% 0.20/0.44  # ...of these trivial                  : 11
% 0.20/0.44  # ...subsumed                          : 398
% 0.20/0.44  # ...remaining for further processing  : 385
% 0.20/0.44  # Other redundant clauses eliminated   : 13
% 0.20/0.44  # Clauses deleted for lack of memory   : 0
% 0.20/0.44  # Backward-subsumed                    : 42
% 0.20/0.44  # Backward-rewritten                   : 147
% 0.20/0.44  # Generated clauses                    : 2215
% 0.20/0.44  # ...of the previous two non-trivial   : 1810
% 0.20/0.44  # Contextual simplify-reflections      : 18
% 0.20/0.44  # Paramodulations                      : 2153
% 0.20/0.44  # Factorizations                       : 43
% 0.20/0.44  # Equation resolutions                 : 18
% 0.20/0.44  # Propositional unsat checks           : 0
% 0.20/0.44  #    Propositional check models        : 0
% 0.20/0.44  #    Propositional check unsatisfiable : 0
% 0.20/0.44  #    Propositional clauses             : 0
% 0.20/0.44  #    Propositional clauses after purity: 0
% 0.20/0.44  #    Propositional unsat core size     : 0
% 0.20/0.44  #    Propositional preprocessing time  : 0.000
% 0.20/0.44  #    Propositional encoding time       : 0.000
% 0.20/0.44  #    Propositional solver time         : 0.000
% 0.20/0.44  #    Success case prop preproc time    : 0.000
% 0.20/0.44  #    Success case prop encoding time   : 0.000
% 0.20/0.44  #    Success case prop solver time     : 0.000
% 0.20/0.44  # Current number of processed clauses  : 193
% 0.20/0.44  #    Positive orientable unit clauses  : 23
% 0.20/0.44  #    Positive unorientable unit clauses: 0
% 0.20/0.44  #    Negative unit clauses             : 1
% 0.20/0.44  #    Non-unit-clauses                  : 169
% 0.20/0.44  # Current number of unprocessed clauses: 1036
% 0.20/0.44  # ...number of literals in the above   : 4201
% 0.20/0.44  # Current number of archived formulas  : 0
% 0.20/0.44  # Current number of archived clauses   : 190
% 0.20/0.44  # Clause-clause subsumption calls (NU) : 6884
% 0.20/0.44  # Rec. Clause-clause subsumption calls : 3899
% 0.20/0.44  # Non-unit clause-clause subsumptions  : 453
% 0.20/0.44  # Unit Clause-clause subsumption calls : 313
% 0.20/0.44  # Rewrite failures with RHS unbound    : 0
% 0.20/0.44  # BW rewrite match attempts            : 15
% 0.20/0.44  # BW rewrite match successes           : 9
% 0.20/0.44  # Condensation attempts                : 0
% 0.20/0.44  # Condensation successes               : 0
% 0.20/0.44  # Termbank termtop insertions          : 26463
% 0.20/0.44  
% 0.20/0.44  # -------------------------------------------------
% 0.20/0.44  # User time                : 0.099 s
% 0.20/0.44  # System time              : 0.003 s
% 0.20/0.44  # Total time               : 0.102 s
% 0.20/0.44  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
