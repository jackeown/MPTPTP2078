%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:02 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 (8284 expanded)
%              Number of clauses        :   57 (3127 expanded)
%              Number of leaves         :   26 (2483 expanded)
%              Depth                    :   12
%              Number of atoms          :  307 (14296 expanded)
%              Number of equality atoms :  145 (8212 expanded)
%              Maximal formula depth    :   47 (   4 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,k1_tarski(X1),X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t117_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(t13_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( r1_tarski(k1_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(t144_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(d6_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( X9 = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X10 != X1
              & X10 != X2
              & X10 != X3
              & X10 != X4
              & X10 != X5
              & X10 != X6
              & X10 != X7
              & X10 != X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t150_relat_1,axiom,(
    ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,k1_tarski(X1),X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t64_funct_2])).

fof(c_0_27,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,k1_tarski(esk2_0),esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)))
    & esk3_0 != k1_xboole_0
    & ~ r1_tarski(k7_relset_1(k1_tarski(esk2_0),esk3_0,esk5_0,esk4_0),k1_tarski(k1_funct_1(esk5_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_28,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_29,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_30,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_31,plain,(
    ! [X20,X21,X22,X23] : k3_enumset1(X20,X20,X21,X22,X23) = k2_enumset1(X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_32,plain,(
    ! [X24,X25,X26,X27,X28] : k4_enumset1(X24,X24,X25,X26,X27,X28) = k3_enumset1(X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_33,plain,(
    ! [X29,X30,X31,X32,X33,X34] : k5_enumset1(X29,X29,X30,X31,X32,X33,X34) = k4_enumset1(X29,X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_34,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41] : k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41) = k5_enumset1(X35,X36,X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_35,plain,(
    ! [X84,X85] :
      ( ~ v1_relat_1(X85)
      | ~ v1_funct_1(X85)
      | ~ r2_hidden(X84,k1_relat_1(X85))
      | k11_relat_1(X85,X84) = k1_tarski(k1_funct_1(X85,X84)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_funct_1])])).

fof(c_0_36,plain,(
    ! [X69,X70] :
      ( ~ v1_relat_1(X69)
      | ~ m1_subset_1(X70,k1_zfmisc_1(X69))
      | v1_relat_1(X70) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_45,plain,(
    ! [X75,X76] : v1_relat_1(k2_zfmisc_1(X75,X76)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_46,plain,(
    ! [X79,X80] :
      ( ~ v1_relat_1(X80)
      | k2_relat_1(k7_relat_1(X80,X79)) = k9_relat_1(X80,X79) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_47,plain,(
    ! [X82,X83] :
      ( ~ v1_relat_1(X83)
      | ~ v4_relat_1(X83,X82)
      | X83 = k7_relat_1(X83,X82) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

fof(c_0_48,plain,(
    ! [X86,X87,X88] :
      ( ( v4_relat_1(X88,X86)
        | ~ m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X86,X87))) )
      & ( v5_relat_1(X88,X87)
        | ~ m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X86,X87))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(esk2_0),esk3_0,esk5_0,esk4_0),k1_tarski(k1_funct_1(esk5_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_50,plain,
    ( k11_relat_1(X1,X2) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_51,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_53,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_54,plain,(
    ! [X89,X90,X91,X92] :
      ( ~ m1_subset_1(X91,k1_zfmisc_1(k2_zfmisc_1(X89,X90)))
      | k7_relset_1(X89,X90,X91,X92) = k9_relat_1(X91,X92) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_55,plain,(
    ! [X71,X72] :
      ( ~ v1_relat_1(X71)
      | k11_relat_1(X71,X72) = k9_relat_1(X71,k1_tarski(X72)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

cnf(c_0_56,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_59,plain,(
    ! [X93,X94,X95,X96] :
      ( ~ m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X93,X95)))
      | ~ r1_tarski(k1_relat_1(X96),X94)
      | m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X94,X95))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,esk4_0),k6_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44])).

cnf(c_0_61,plain,
    ( k11_relat_1(X1,X2) = k6_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_63,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_64,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,plain,
    ( k2_relat_1(X1) = k9_relat_1(X1,X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( v4_relat_1(esk5_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_52])).

fof(c_0_68,plain,(
    ! [X42,X43] :
      ( ( ~ r1_tarski(X42,k1_tarski(X43))
        | X42 = k1_xboole_0
        | X42 = k1_tarski(X43) )
      & ( X42 != k1_xboole_0
        | r1_tarski(X42,k1_tarski(X43)) )
      & ( X42 != k1_tarski(X43)
        | r1_tarski(X42,k1_tarski(X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_69,plain,(
    ! [X67,X68] :
      ( ( ~ m1_subset_1(X67,k1_zfmisc_1(X68))
        | r1_tarski(X67,X68) )
      & ( ~ r1_tarski(X67,X68)
        | m1_subset_1(X67,k1_zfmisc_1(X68)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k1_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_71,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_relat_1(esk5_0))
    | ~ r1_tarski(k7_relset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,esk4_0),k11_relat_1(esk5_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_73,negated_conjecture,
    ( k7_relset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,X1) = k9_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_52])).

cnf(c_0_74,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_75,negated_conjecture,
    ( k9_relat_1(esk5_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) = k2_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_63])])).

cnf(c_0_76,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_77,plain,(
    ! [X73,X74] :
      ( ( ~ v4_relat_1(X74,X73)
        | r1_tarski(k1_relat_1(X74),X73)
        | ~ v1_relat_1(X74) )
      & ( ~ r1_tarski(k1_relat_1(X74),X73)
        | v4_relat_1(X74,X73)
        | ~ v1_relat_1(X74) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ r1_tarski(k1_relat_1(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_52])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_relat_1(esk5_0))
    | ~ r1_tarski(k9_relat_1(esk5_0,esk4_0),k11_relat_1(esk5_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( k11_relat_1(esk5_0,esk2_0) = k2_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_63])])).

fof(c_0_83,plain,(
    ! [X77,X78] :
      ( ~ v1_relat_1(X78)
      | r1_tarski(k9_relat_1(X78,X77),k2_relat_1(X78)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).

cnf(c_0_84,plain,
    ( X1 = k1_xboole_0
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44])).

cnf(c_0_85,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

fof(c_0_86,plain,(
    ! [X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58,X59,X60,X61,X62,X63,X64,X65] :
      ( ( ~ r2_hidden(X55,X54)
        | X55 = X46
        | X55 = X47
        | X55 = X48
        | X55 = X49
        | X55 = X50
        | X55 = X51
        | X55 = X52
        | X55 = X53
        | X54 != k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( X56 != X46
        | r2_hidden(X56,X54)
        | X54 != k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( X56 != X47
        | r2_hidden(X56,X54)
        | X54 != k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( X56 != X48
        | r2_hidden(X56,X54)
        | X54 != k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( X56 != X49
        | r2_hidden(X56,X54)
        | X54 != k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( X56 != X50
        | r2_hidden(X56,X54)
        | X54 != k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( X56 != X51
        | r2_hidden(X56,X54)
        | X54 != k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( X56 != X52
        | r2_hidden(X56,X54)
        | X54 != k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( X56 != X53
        | r2_hidden(X56,X54)
        | X54 != k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53) )
      & ( esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65) != X57
        | ~ r2_hidden(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | X65 = k6_enumset1(X57,X58,X59,X60,X61,X62,X63,X64) )
      & ( esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65) != X58
        | ~ r2_hidden(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | X65 = k6_enumset1(X57,X58,X59,X60,X61,X62,X63,X64) )
      & ( esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65) != X59
        | ~ r2_hidden(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | X65 = k6_enumset1(X57,X58,X59,X60,X61,X62,X63,X64) )
      & ( esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65) != X60
        | ~ r2_hidden(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | X65 = k6_enumset1(X57,X58,X59,X60,X61,X62,X63,X64) )
      & ( esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65) != X61
        | ~ r2_hidden(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | X65 = k6_enumset1(X57,X58,X59,X60,X61,X62,X63,X64) )
      & ( esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65) != X62
        | ~ r2_hidden(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | X65 = k6_enumset1(X57,X58,X59,X60,X61,X62,X63,X64) )
      & ( esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65) != X63
        | ~ r2_hidden(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | X65 = k6_enumset1(X57,X58,X59,X60,X61,X62,X63,X64) )
      & ( esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65) != X64
        | ~ r2_hidden(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | X65 = k6_enumset1(X57,X58,X59,X60,X61,X62,X63,X64) )
      & ( r2_hidden(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65) = X57
        | esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65) = X58
        | esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65) = X59
        | esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65) = X60
        | esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65) = X61
        | esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65) = X62
        | esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65) = X63
        | esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65) = X64
        | X65 = k6_enumset1(X57,X58,X59,X60,X61,X62,X63,X64) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(X1,esk3_0))
    | ~ r1_tarski(k1_relat_1(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_88,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_89,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_relat_1(esk5_0))
    | ~ r1_tarski(k9_relat_1(esk5_0,esk4_0),k2_relat_1(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_90,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_91,plain,
    ( k1_relat_1(X1) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | k1_relat_1(X1) = k1_xboole_0
    | ~ v4_relat_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

fof(c_0_93,plain,(
    ! [X44,X45] :
      ( ( k2_zfmisc_1(X44,X45) != k1_xboole_0
        | X44 = k1_xboole_0
        | X45 = k1_xboole_0 )
      & ( X44 != k1_xboole_0
        | k2_zfmisc_1(X44,X45) = k1_xboole_0 )
      & ( X45 != k1_xboole_0
        | k2_zfmisc_1(X44,X45) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_94,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(k1_relat_1(esk5_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_96,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_63])])).

cnf(c_0_97,negated_conjecture,
    ( k1_relat_1(esk5_0) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)
    | k1_relat_1(esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_67]),c_0_63])])).

cnf(c_0_98,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_92])])).

cnf(c_0_99,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

fof(c_0_100,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_101,negated_conjecture,
    ( k2_zfmisc_1(k1_relat_1(esk5_0),esk3_0) = esk5_0
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk5_0),esk3_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_102,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])])).

cnf(c_0_103,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_99])).

cnf(c_0_104,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

fof(c_0_105,plain,(
    ! [X81] : k9_relat_1(k1_xboole_0,X81) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t150_relat_1])).

cnf(c_0_106,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk5_0,esk4_0),k6_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_60,c_0_73])).

cnf(c_0_107,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_102]),c_0_103]),c_0_102]),c_0_103]),c_0_104])])).

cnf(c_0_108,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_107]),c_0_108]),c_0_107]),c_0_107]),c_0_107]),c_0_107]),c_0_107]),c_0_107]),c_0_107]),c_0_107]),c_0_104])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.029 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t64_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 0.20/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.39  fof(t117_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k11_relat_1(X2,X1)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 0.20/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.39  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.20/0.39  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.20/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.39  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.20/0.39  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 0.20/0.39  fof(t13_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>(r1_tarski(k1_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 0.20/0.39  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.20/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.39  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.20/0.39  fof(t144_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 0.20/0.39  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 0.20/0.39  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.39  fof(t150_relat_1, axiom, ![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 0.20/0.39  fof(c_0_26, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1)))))), inference(assume_negation,[status(cth)],[t64_funct_2])).
% 0.20/0.39  fof(c_0_27, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,k1_tarski(esk2_0),esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))))&(esk3_0!=k1_xboole_0&~r1_tarski(k7_relset_1(k1_tarski(esk2_0),esk3_0,esk5_0,esk4_0),k1_tarski(k1_funct_1(esk5_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.20/0.39  fof(c_0_28, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.39  fof(c_0_29, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.39  fof(c_0_30, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.39  fof(c_0_31, plain, ![X20, X21, X22, X23]:k3_enumset1(X20,X20,X21,X22,X23)=k2_enumset1(X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.39  fof(c_0_32, plain, ![X24, X25, X26, X27, X28]:k4_enumset1(X24,X24,X25,X26,X27,X28)=k3_enumset1(X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.39  fof(c_0_33, plain, ![X29, X30, X31, X32, X33, X34]:k5_enumset1(X29,X29,X30,X31,X32,X33,X34)=k4_enumset1(X29,X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.39  fof(c_0_34, plain, ![X35, X36, X37, X38, X39, X40, X41]:k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41)=k5_enumset1(X35,X36,X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.39  fof(c_0_35, plain, ![X84, X85]:(~v1_relat_1(X85)|~v1_funct_1(X85)|(~r2_hidden(X84,k1_relat_1(X85))|k11_relat_1(X85,X84)=k1_tarski(k1_funct_1(X85,X84)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_funct_1])])).
% 0.20/0.39  fof(c_0_36, plain, ![X69, X70]:(~v1_relat_1(X69)|(~m1_subset_1(X70,k1_zfmisc_1(X69))|v1_relat_1(X70))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_38, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_39, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  cnf(c_0_40, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_41, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.39  cnf(c_0_42, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.39  cnf(c_0_43, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.39  cnf(c_0_44, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.39  fof(c_0_45, plain, ![X75, X76]:v1_relat_1(k2_zfmisc_1(X75,X76)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.39  fof(c_0_46, plain, ![X79, X80]:(~v1_relat_1(X80)|k2_relat_1(k7_relat_1(X80,X79))=k9_relat_1(X80,X79)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.20/0.39  fof(c_0_47, plain, ![X82, X83]:(~v1_relat_1(X83)|~v4_relat_1(X83,X82)|X83=k7_relat_1(X83,X82)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.20/0.39  fof(c_0_48, plain, ![X86, X87, X88]:((v4_relat_1(X88,X86)|~m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X86,X87))))&(v5_relat_1(X88,X87)|~m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X86,X87))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (~r1_tarski(k7_relset_1(k1_tarski(esk2_0),esk3_0,esk5_0,esk4_0),k1_tarski(k1_funct_1(esk5_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_50, plain, (k11_relat_1(X1,X2)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.39  cnf(c_0_51, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.20/0.39  cnf(c_0_53, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.39  fof(c_0_54, plain, ![X89, X90, X91, X92]:(~m1_subset_1(X91,k1_zfmisc_1(k2_zfmisc_1(X89,X90)))|k7_relset_1(X89,X90,X91,X92)=k9_relat_1(X91,X92)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.20/0.39  fof(c_0_55, plain, ![X71, X72]:(~v1_relat_1(X71)|k11_relat_1(X71,X72)=k9_relat_1(X71,k1_tarski(X72))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.20/0.39  cnf(c_0_56, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.39  cnf(c_0_57, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.39  cnf(c_0_58, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.39  fof(c_0_59, plain, ![X93, X94, X95, X96]:(~m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X93,X95)))|(~r1_tarski(k1_relat_1(X96),X94)|m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X94,X95))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (~r1_tarski(k7_relset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,esk4_0),k6_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44])).
% 0.20/0.39  cnf(c_0_61, plain, (k11_relat_1(X1,X2)=k6_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.20/0.39  cnf(c_0_64, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.39  cnf(c_0_65, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.39  cnf(c_0_66, plain, (k2_relat_1(X1)=k9_relat_1(X1,X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.39  cnf(c_0_67, negated_conjecture, (v4_relat_1(esk5_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_58, c_0_52])).
% 0.20/0.39  fof(c_0_68, plain, ![X42, X43]:((~r1_tarski(X42,k1_tarski(X43))|(X42=k1_xboole_0|X42=k1_tarski(X43)))&((X42!=k1_xboole_0|r1_tarski(X42,k1_tarski(X43)))&(X42!=k1_tarski(X43)|r1_tarski(X42,k1_tarski(X43))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.20/0.39  fof(c_0_69, plain, ![X67, X68]:((~m1_subset_1(X67,k1_zfmisc_1(X68))|r1_tarski(X67,X68))&(~r1_tarski(X67,X68)|m1_subset_1(X67,k1_zfmisc_1(X68)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.39  cnf(c_0_70, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k1_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.39  fof(c_0_71, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.39  cnf(c_0_72, negated_conjecture, (~r2_hidden(esk2_0,k1_relat_1(esk5_0))|~r1_tarski(k7_relset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,esk4_0),k11_relat_1(esk5_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_63])])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, (k7_relset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,X1)=k9_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_64, c_0_52])).
% 0.20/0.39  cnf(c_0_74, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.20/0.39  cnf(c_0_75, negated_conjecture, (k9_relat_1(esk5_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))=k2_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_63])])).
% 0.20/0.39  cnf(c_0_76, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.39  fof(c_0_77, plain, ![X73, X74]:((~v4_relat_1(X74,X73)|r1_tarski(k1_relat_1(X74),X73)|~v1_relat_1(X74))&(~r1_tarski(k1_relat_1(X74),X73)|v4_relat_1(X74,X73)|~v1_relat_1(X74))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.20/0.39  cnf(c_0_78, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.39  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))|~r1_tarski(k1_relat_1(esk5_0),X1)), inference(spm,[status(thm)],[c_0_70, c_0_52])).
% 0.20/0.39  cnf(c_0_80, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.39  cnf(c_0_81, negated_conjecture, (~r2_hidden(esk2_0,k1_relat_1(esk5_0))|~r1_tarski(k9_relat_1(esk5_0,esk4_0),k11_relat_1(esk5_0,esk2_0))), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 0.20/0.39  cnf(c_0_82, negated_conjecture, (k11_relat_1(esk5_0,esk2_0)=k2_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_63])])).
% 0.20/0.39  fof(c_0_83, plain, ![X77, X78]:(~v1_relat_1(X78)|r1_tarski(k9_relat_1(X78,X77),k2_relat_1(X78))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).
% 0.20/0.39  cnf(c_0_84, plain, (X1=k1_xboole_0|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44])).
% 0.20/0.39  cnf(c_0_85, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.39  fof(c_0_86, plain, ![X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59, X60, X61, X62, X63, X64, X65]:(((~r2_hidden(X55,X54)|(X55=X46|X55=X47|X55=X48|X55=X49|X55=X50|X55=X51|X55=X52|X55=X53)|X54!=k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53))&((((((((X56!=X46|r2_hidden(X56,X54)|X54!=k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53))&(X56!=X47|r2_hidden(X56,X54)|X54!=k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53)))&(X56!=X48|r2_hidden(X56,X54)|X54!=k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53)))&(X56!=X49|r2_hidden(X56,X54)|X54!=k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53)))&(X56!=X50|r2_hidden(X56,X54)|X54!=k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53)))&(X56!=X51|r2_hidden(X56,X54)|X54!=k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53)))&(X56!=X52|r2_hidden(X56,X54)|X54!=k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53)))&(X56!=X53|r2_hidden(X56,X54)|X54!=k6_enumset1(X46,X47,X48,X49,X50,X51,X52,X53))))&(((((((((esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65)!=X57|~r2_hidden(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|X65=k6_enumset1(X57,X58,X59,X60,X61,X62,X63,X64))&(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65)!=X58|~r2_hidden(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|X65=k6_enumset1(X57,X58,X59,X60,X61,X62,X63,X64)))&(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65)!=X59|~r2_hidden(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|X65=k6_enumset1(X57,X58,X59,X60,X61,X62,X63,X64)))&(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65)!=X60|~r2_hidden(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|X65=k6_enumset1(X57,X58,X59,X60,X61,X62,X63,X64)))&(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65)!=X61|~r2_hidden(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|X65=k6_enumset1(X57,X58,X59,X60,X61,X62,X63,X64)))&(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65)!=X62|~r2_hidden(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|X65=k6_enumset1(X57,X58,X59,X60,X61,X62,X63,X64)))&(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65)!=X63|~r2_hidden(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|X65=k6_enumset1(X57,X58,X59,X60,X61,X62,X63,X64)))&(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65)!=X64|~r2_hidden(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|X65=k6_enumset1(X57,X58,X59,X60,X61,X62,X63,X64)))&(r2_hidden(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|(esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65)=X57|esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65)=X58|esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65)=X59|esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65)=X60|esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65)=X61|esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65)=X62|esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65)=X63|esk1_9(X57,X58,X59,X60,X61,X62,X63,X64,X65)=X64)|X65=k6_enumset1(X57,X58,X59,X60,X61,X62,X63,X64)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.20/0.39  cnf(c_0_87, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(X1,esk3_0))|~r1_tarski(k1_relat_1(esk5_0),X1)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.20/0.39  cnf(c_0_88, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_80])).
% 0.20/0.39  cnf(c_0_89, negated_conjecture, (~r2_hidden(esk2_0,k1_relat_1(esk5_0))|~r1_tarski(k9_relat_1(esk5_0,esk4_0),k2_relat_1(esk5_0))), inference(rw,[status(thm)],[c_0_81, c_0_82])).
% 0.20/0.39  cnf(c_0_90, plain, (r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.20/0.39  cnf(c_0_91, plain, (k1_relat_1(X1)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|k1_relat_1(X1)=k1_xboole_0|~v4_relat_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.20/0.39  cnf(c_0_92, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.20/0.39  fof(c_0_93, plain, ![X44, X45]:((k2_zfmisc_1(X44,X45)!=k1_xboole_0|(X44=k1_xboole_0|X45=k1_xboole_0))&((X44!=k1_xboole_0|k2_zfmisc_1(X44,X45)=k1_xboole_0)&(X45!=k1_xboole_0|k2_zfmisc_1(X44,X45)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.39  cnf(c_0_94, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.39  cnf(c_0_95, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(k1_relat_1(esk5_0),esk3_0))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.20/0.39  cnf(c_0_96, negated_conjecture, (~r2_hidden(esk2_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_63])])).
% 0.20/0.39  cnf(c_0_97, negated_conjecture, (k1_relat_1(esk5_0)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)|k1_relat_1(esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_67]), c_0_63])])).
% 0.20/0.39  cnf(c_0_98, plain, (r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_92])])).
% 0.20/0.39  cnf(c_0_99, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.20/0.39  fof(c_0_100, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.39  cnf(c_0_101, negated_conjecture, (k2_zfmisc_1(k1_relat_1(esk5_0),esk3_0)=esk5_0|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk5_0),esk3_0),esk5_0)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.20/0.39  cnf(c_0_102, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])])).
% 0.20/0.39  cnf(c_0_103, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_99])).
% 0.20/0.39  cnf(c_0_104, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.20/0.39  fof(c_0_105, plain, ![X81]:k9_relat_1(k1_xboole_0,X81)=k1_xboole_0, inference(variable_rename,[status(thm)],[t150_relat_1])).
% 0.20/0.39  cnf(c_0_106, negated_conjecture, (~r1_tarski(k9_relat_1(esk5_0,esk4_0),k6_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0)))), inference(rw,[status(thm)],[c_0_60, c_0_73])).
% 0.20/0.39  cnf(c_0_107, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_102]), c_0_103]), c_0_102]), c_0_103]), c_0_104])])).
% 0.20/0.39  cnf(c_0_108, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_105])).
% 0.20/0.39  cnf(c_0_109, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_107]), c_0_108]), c_0_107]), c_0_107]), c_0_107]), c_0_107]), c_0_107]), c_0_107]), c_0_107]), c_0_107]), c_0_104])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 110
% 0.20/0.39  # Proof object clause steps            : 57
% 0.20/0.39  # Proof object formula steps           : 53
% 0.20/0.39  # Proof object conjectures             : 26
% 0.20/0.39  # Proof object clause conjectures      : 23
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 29
% 0.20/0.39  # Proof object initial formulas used   : 26
% 0.20/0.39  # Proof object generating inferences   : 15
% 0.20/0.39  # Proof object simplifying inferences  : 89
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 26
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 56
% 0.20/0.39  # Removed in clause preprocessing      : 7
% 0.20/0.39  # Initial clauses in saturation        : 49
% 0.20/0.39  # Processed clauses                    : 267
% 0.20/0.39  # ...of these trivial                  : 3
% 0.20/0.39  # ...subsumed                          : 50
% 0.20/0.39  # ...remaining for further processing  : 214
% 0.20/0.39  # Other redundant clauses eliminated   : 23
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 5
% 0.20/0.39  # Backward-rewritten                   : 53
% 0.20/0.39  # Generated clauses                    : 373
% 0.20/0.39  # ...of the previous two non-trivial   : 272
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 357
% 0.20/0.39  # Factorizations                       : 1
% 0.20/0.39  # Equation resolutions                 : 23
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 95
% 0.20/0.39  #    Positive orientable unit clauses  : 27
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 1
% 0.20/0.39  #    Non-unit-clauses                  : 67
% 0.20/0.39  # Current number of unprocessed clauses: 99
% 0.20/0.39  # ...number of literals in the above   : 318
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 111
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 1762
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 1541
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 53
% 0.20/0.39  # Unit Clause-clause subsumption calls : 71
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 73
% 0.20/0.39  # BW rewrite match successes           : 6
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 8525
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.043 s
% 0.20/0.39  # System time              : 0.006 s
% 0.20/0.39  # Total time               : 0.049 s
% 0.20/0.39  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
