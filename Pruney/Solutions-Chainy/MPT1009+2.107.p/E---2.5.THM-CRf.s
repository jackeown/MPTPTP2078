%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:02 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  111 (8410 expanded)
%              Number of clauses        :   58 (3181 expanded)
%              Number of leaves         :   26 (2519 expanded)
%              Depth                    :   12
%              Number of atoms          :  292 (14134 expanded)
%              Number of equality atoms :  133 (8104 expanded)
%              Maximal formula depth    :   37 (   4 average)
%              Maximal clause size      :   52 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,k1_tarski(X1),X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t117_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(t13_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( r1_tarski(k1_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d4_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] :
      ( X7 = k4_enumset1(X1,X2,X3,X4,X5,X6)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X8 != X1
              & X8 != X2
              & X8 != X3
              & X8 != X4
              & X8 != X5
              & X8 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(t144_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t150_relat_1,axiom,(
    ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

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
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_29,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_30,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_31,plain,(
    ! [X18,X19,X20,X21] : k3_enumset1(X18,X18,X19,X20,X21) = k2_enumset1(X18,X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_32,plain,(
    ! [X22,X23,X24,X25,X26] : k4_enumset1(X22,X22,X23,X24,X25,X26) = k3_enumset1(X22,X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_33,plain,(
    ! [X27,X28,X29,X30,X31,X32] : k5_enumset1(X27,X27,X28,X29,X30,X31,X32) = k4_enumset1(X27,X28,X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_34,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39] : k6_enumset1(X33,X33,X34,X35,X36,X37,X38,X39) = k5_enumset1(X33,X34,X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_35,plain,(
    ! [X78,X79] :
      ( ~ v1_relat_1(X79)
      | ~ v1_funct_1(X79)
      | ~ r2_hidden(X78,k1_relat_1(X79))
      | k11_relat_1(X79,X78) = k1_tarski(k1_funct_1(X79,X78)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_funct_1])])).

fof(c_0_36,plain,(
    ! [X63,X64] :
      ( ~ v1_relat_1(X63)
      | ~ m1_subset_1(X64,k1_zfmisc_1(X63))
      | v1_relat_1(X64) ) ),
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
    ! [X69,X70] : v1_relat_1(k2_zfmisc_1(X69,X70)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_46,plain,(
    ! [X73,X74] :
      ( ~ v1_relat_1(X74)
      | k2_relat_1(k7_relat_1(X74,X73)) = k9_relat_1(X74,X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_47,plain,(
    ! [X76,X77] :
      ( ~ v1_relat_1(X77)
      | ~ v4_relat_1(X77,X76)
      | X77 = k7_relat_1(X77,X76) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

fof(c_0_48,plain,(
    ! [X80,X81,X82] :
      ( ( v4_relat_1(X82,X80)
        | ~ m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) )
      & ( v5_relat_1(X82,X81)
        | ~ m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) ) ) ),
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
    ! [X83,X84,X85,X86] :
      ( ~ m1_subset_1(X85,k1_zfmisc_1(k2_zfmisc_1(X83,X84)))
      | k7_relset_1(X83,X84,X85,X86) = k9_relat_1(X85,X86) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_55,plain,(
    ! [X65,X66] :
      ( ~ v1_relat_1(X65)
      | k11_relat_1(X65,X66) = k9_relat_1(X65,k1_tarski(X66)) ) ),
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
    ! [X87,X88,X89,X90] :
      ( ~ m1_subset_1(X90,k1_zfmisc_1(k2_zfmisc_1(X87,X89)))
      | ~ r1_tarski(k1_relat_1(X90),X88)
      | m1_subset_1(X90,k1_zfmisc_1(k2_zfmisc_1(X88,X89))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).

fof(c_0_60,plain,(
    ! [X40,X41] :
      ( ( ~ r1_tarski(X40,k1_tarski(X41))
        | X40 = k1_xboole_0
        | X40 = k1_tarski(X41) )
      & ( X40 != k1_xboole_0
        | r1_tarski(X40,k1_tarski(X41)) )
      & ( X40 != k1_tarski(X41)
        | r1_tarski(X40,k1_tarski(X41)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,esk4_0),k6_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44])).

cnf(c_0_62,plain,
    ( k11_relat_1(X1,X2) = k6_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_64,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_65,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_66,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_67,plain,
    ( k2_relat_1(X1) = k9_relat_1(X1,X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_68,negated_conjecture,
    ( v4_relat_1(esk5_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_52])).

fof(c_0_69,plain,(
    ! [X61,X62] :
      ( ( ~ m1_subset_1(X61,k1_zfmisc_1(X62))
        | r1_tarski(X61,X62) )
      & ( ~ r1_tarski(X61,X62)
        | m1_subset_1(X61,k1_zfmisc_1(X62)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k1_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_71,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_72,plain,(
    ! [X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58,X59] :
      ( ( ~ r2_hidden(X51,X50)
        | X51 = X44
        | X51 = X45
        | X51 = X46
        | X51 = X47
        | X51 = X48
        | X51 = X49
        | X50 != k4_enumset1(X44,X45,X46,X47,X48,X49) )
      & ( X52 != X44
        | r2_hidden(X52,X50)
        | X50 != k4_enumset1(X44,X45,X46,X47,X48,X49) )
      & ( X52 != X45
        | r2_hidden(X52,X50)
        | X50 != k4_enumset1(X44,X45,X46,X47,X48,X49) )
      & ( X52 != X46
        | r2_hidden(X52,X50)
        | X50 != k4_enumset1(X44,X45,X46,X47,X48,X49) )
      & ( X52 != X47
        | r2_hidden(X52,X50)
        | X50 != k4_enumset1(X44,X45,X46,X47,X48,X49) )
      & ( X52 != X48
        | r2_hidden(X52,X50)
        | X50 != k4_enumset1(X44,X45,X46,X47,X48,X49) )
      & ( X52 != X49
        | r2_hidden(X52,X50)
        | X50 != k4_enumset1(X44,X45,X46,X47,X48,X49) )
      & ( esk1_7(X53,X54,X55,X56,X57,X58,X59) != X53
        | ~ r2_hidden(esk1_7(X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k4_enumset1(X53,X54,X55,X56,X57,X58) )
      & ( esk1_7(X53,X54,X55,X56,X57,X58,X59) != X54
        | ~ r2_hidden(esk1_7(X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k4_enumset1(X53,X54,X55,X56,X57,X58) )
      & ( esk1_7(X53,X54,X55,X56,X57,X58,X59) != X55
        | ~ r2_hidden(esk1_7(X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k4_enumset1(X53,X54,X55,X56,X57,X58) )
      & ( esk1_7(X53,X54,X55,X56,X57,X58,X59) != X56
        | ~ r2_hidden(esk1_7(X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k4_enumset1(X53,X54,X55,X56,X57,X58) )
      & ( esk1_7(X53,X54,X55,X56,X57,X58,X59) != X57
        | ~ r2_hidden(esk1_7(X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k4_enumset1(X53,X54,X55,X56,X57,X58) )
      & ( esk1_7(X53,X54,X55,X56,X57,X58,X59) != X58
        | ~ r2_hidden(esk1_7(X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k4_enumset1(X53,X54,X55,X56,X57,X58) )
      & ( r2_hidden(esk1_7(X53,X54,X55,X56,X57,X58,X59),X59)
        | esk1_7(X53,X54,X55,X56,X57,X58,X59) = X53
        | esk1_7(X53,X54,X55,X56,X57,X58,X59) = X54
        | esk1_7(X53,X54,X55,X56,X57,X58,X59) = X55
        | esk1_7(X53,X54,X55,X56,X57,X58,X59) = X56
        | esk1_7(X53,X54,X55,X56,X57,X58,X59) = X57
        | esk1_7(X53,X54,X55,X56,X57,X58,X59) = X58
        | X59 = k4_enumset1(X53,X54,X55,X56,X57,X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_74,plain,(
    ! [X67,X68] :
      ( ( ~ v4_relat_1(X68,X67)
        | r1_tarski(k1_relat_1(X68),X67)
        | ~ v1_relat_1(X68) )
      & ( ~ r1_tarski(k1_relat_1(X68),X67)
        | v4_relat_1(X68,X67)
        | ~ v1_relat_1(X68) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_relat_1(esk5_0))
    | ~ r1_tarski(k7_relset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,esk4_0),k11_relat_1(esk5_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64])])).

cnf(c_0_76,negated_conjecture,
    ( k7_relset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,X1) = k9_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_52])).

cnf(c_0_77,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_78,negated_conjecture,
    ( k9_relat_1(esk5_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) = k2_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_64])])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ r1_tarski(k1_relat_1(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_52])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X2,X4,X5,X6,X7,X8) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_83,plain,
    ( X1 = k1_xboole_0
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44])).

cnf(c_0_84,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_85,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_relat_1(esk5_0))
    | ~ r1_tarski(k9_relat_1(esk5_0,esk4_0),k11_relat_1(esk5_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_86,negated_conjecture,
    ( k11_relat_1(esk5_0,esk2_0) = k2_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_64])])).

fof(c_0_87,plain,(
    ! [X71,X72] :
      ( ~ v1_relat_1(X72)
      | r1_tarski(k9_relat_1(X72,X71),k2_relat_1(X72)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(X1,esk3_0))
    | ~ r1_tarski(k1_relat_1(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X2,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_43]),c_0_44])).

cnf(c_0_91,plain,
    ( k1_relat_1(X1) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | k1_relat_1(X1) = k1_xboole_0
    | ~ v4_relat_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_relat_1(esk5_0))
    | ~ r1_tarski(k9_relat_1(esk5_0,esk4_0),k2_relat_1(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_93,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

fof(c_0_94,plain,(
    ! [X42,X43] :
      ( ( k2_zfmisc_1(X42,X43) != k1_xboole_0
        | X42 = k1_xboole_0
        | X43 = k1_xboole_0 )
      & ( X42 != k1_xboole_0
        | k2_zfmisc_1(X42,X43) = k1_xboole_0 )
      & ( X43 != k1_xboole_0
        | k2_zfmisc_1(X42,X43) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_95,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(k1_relat_1(esk5_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_97,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_90])])).

cnf(c_0_98,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = k1_relat_1(esk5_0)
    | k1_relat_1(esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_68]),c_0_64])])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_64])])).

cnf(c_0_100,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

fof(c_0_101,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_102,negated_conjecture,
    ( k2_zfmisc_1(k1_relat_1(esk5_0),esk3_0) = esk5_0
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk5_0),esk3_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_103,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])).

cnf(c_0_104,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_100])).

cnf(c_0_105,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

fof(c_0_106,plain,(
    ! [X75] : k9_relat_1(k1_xboole_0,X75) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t150_relat_1])).

cnf(c_0_107,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk5_0,esk4_0),k6_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_61,c_0_76])).

cnf(c_0_108,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103]),c_0_104]),c_0_103]),c_0_104]),c_0_105])])).

cnf(c_0_109,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_108]),c_0_109]),c_0_108]),c_0_108]),c_0_108]),c_0_108]),c_0_108]),c_0_108]),c_0_108]),c_0_108]),c_0_105])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:09:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.029 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(t64_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 0.19/0.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.43  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.43  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.43  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.43  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.43  fof(t117_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k11_relat_1(X2,X1)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 0.19/0.43  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.43  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.43  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.19/0.43  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.19/0.43  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.43  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.19/0.43  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 0.19/0.43  fof(t13_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>(r1_tarski(k1_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 0.19/0.43  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.19/0.43  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.43  fof(d4_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:(X7=k4_enumset1(X1,X2,X3,X4,X5,X6)<=>![X8]:(r2_hidden(X8,X7)<=>~((((((X8!=X1&X8!=X2)&X8!=X3)&X8!=X4)&X8!=X5)&X8!=X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 0.19/0.43  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.19/0.43  fof(t144_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 0.19/0.43  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.43  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.43  fof(t150_relat_1, axiom, ![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 0.19/0.43  fof(c_0_26, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1)))))), inference(assume_negation,[status(cth)],[t64_funct_2])).
% 0.19/0.43  fof(c_0_27, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,k1_tarski(esk2_0),esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))))&(esk3_0!=k1_xboole_0&~r1_tarski(k7_relset_1(k1_tarski(esk2_0),esk3_0,esk5_0,esk4_0),k1_tarski(k1_funct_1(esk5_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.19/0.43  fof(c_0_28, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.43  fof(c_0_29, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.43  fof(c_0_30, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.43  fof(c_0_31, plain, ![X18, X19, X20, X21]:k3_enumset1(X18,X18,X19,X20,X21)=k2_enumset1(X18,X19,X20,X21), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.43  fof(c_0_32, plain, ![X22, X23, X24, X25, X26]:k4_enumset1(X22,X22,X23,X24,X25,X26)=k3_enumset1(X22,X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.43  fof(c_0_33, plain, ![X27, X28, X29, X30, X31, X32]:k5_enumset1(X27,X27,X28,X29,X30,X31,X32)=k4_enumset1(X27,X28,X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.43  fof(c_0_34, plain, ![X33, X34, X35, X36, X37, X38, X39]:k6_enumset1(X33,X33,X34,X35,X36,X37,X38,X39)=k5_enumset1(X33,X34,X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.43  fof(c_0_35, plain, ![X78, X79]:(~v1_relat_1(X79)|~v1_funct_1(X79)|(~r2_hidden(X78,k1_relat_1(X79))|k11_relat_1(X79,X78)=k1_tarski(k1_funct_1(X79,X78)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_funct_1])])).
% 0.19/0.43  fof(c_0_36, plain, ![X63, X64]:(~v1_relat_1(X63)|(~m1_subset_1(X64,k1_zfmisc_1(X63))|v1_relat_1(X64))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.43  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.43  cnf(c_0_38, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.43  cnf(c_0_39, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.43  cnf(c_0_40, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.43  cnf(c_0_41, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.43  cnf(c_0_42, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.43  cnf(c_0_43, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.43  cnf(c_0_44, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.43  fof(c_0_45, plain, ![X69, X70]:v1_relat_1(k2_zfmisc_1(X69,X70)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.43  fof(c_0_46, plain, ![X73, X74]:(~v1_relat_1(X74)|k2_relat_1(k7_relat_1(X74,X73))=k9_relat_1(X74,X73)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.19/0.43  fof(c_0_47, plain, ![X76, X77]:(~v1_relat_1(X77)|~v4_relat_1(X77,X76)|X77=k7_relat_1(X77,X76)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.19/0.43  fof(c_0_48, plain, ![X80, X81, X82]:((v4_relat_1(X82,X80)|~m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))))&(v5_relat_1(X82,X81)|~m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X80,X81))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.43  cnf(c_0_49, negated_conjecture, (~r1_tarski(k7_relset_1(k1_tarski(esk2_0),esk3_0,esk5_0,esk4_0),k1_tarski(k1_funct_1(esk5_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.43  cnf(c_0_50, plain, (k11_relat_1(X1,X2)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.43  cnf(c_0_51, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.43  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.19/0.43  cnf(c_0_53, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.43  fof(c_0_54, plain, ![X83, X84, X85, X86]:(~m1_subset_1(X85,k1_zfmisc_1(k2_zfmisc_1(X83,X84)))|k7_relset_1(X83,X84,X85,X86)=k9_relat_1(X85,X86)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.19/0.43  fof(c_0_55, plain, ![X65, X66]:(~v1_relat_1(X65)|k11_relat_1(X65,X66)=k9_relat_1(X65,k1_tarski(X66))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.19/0.43  cnf(c_0_56, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.43  cnf(c_0_57, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.43  cnf(c_0_58, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.43  fof(c_0_59, plain, ![X87, X88, X89, X90]:(~m1_subset_1(X90,k1_zfmisc_1(k2_zfmisc_1(X87,X89)))|(~r1_tarski(k1_relat_1(X90),X88)|m1_subset_1(X90,k1_zfmisc_1(k2_zfmisc_1(X88,X89))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).
% 0.19/0.43  fof(c_0_60, plain, ![X40, X41]:((~r1_tarski(X40,k1_tarski(X41))|(X40=k1_xboole_0|X40=k1_tarski(X41)))&((X40!=k1_xboole_0|r1_tarski(X40,k1_tarski(X41)))&(X40!=k1_tarski(X41)|r1_tarski(X40,k1_tarski(X41))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.19/0.43  cnf(c_0_61, negated_conjecture, (~r1_tarski(k7_relset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,esk4_0),k6_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44])).
% 0.19/0.43  cnf(c_0_62, plain, (k11_relat_1(X1,X2)=k6_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.19/0.43  cnf(c_0_63, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.43  cnf(c_0_64, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.19/0.43  cnf(c_0_65, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.43  cnf(c_0_66, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.43  cnf(c_0_67, plain, (k2_relat_1(X1)=k9_relat_1(X1,X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.43  cnf(c_0_68, negated_conjecture, (v4_relat_1(esk5_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_58, c_0_52])).
% 0.19/0.43  fof(c_0_69, plain, ![X61, X62]:((~m1_subset_1(X61,k1_zfmisc_1(X62))|r1_tarski(X61,X62))&(~r1_tarski(X61,X62)|m1_subset_1(X61,k1_zfmisc_1(X62)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.43  cnf(c_0_70, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k1_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.43  fof(c_0_71, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.43  fof(c_0_72, plain, ![X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59]:(((~r2_hidden(X51,X50)|(X51=X44|X51=X45|X51=X46|X51=X47|X51=X48|X51=X49)|X50!=k4_enumset1(X44,X45,X46,X47,X48,X49))&((((((X52!=X44|r2_hidden(X52,X50)|X50!=k4_enumset1(X44,X45,X46,X47,X48,X49))&(X52!=X45|r2_hidden(X52,X50)|X50!=k4_enumset1(X44,X45,X46,X47,X48,X49)))&(X52!=X46|r2_hidden(X52,X50)|X50!=k4_enumset1(X44,X45,X46,X47,X48,X49)))&(X52!=X47|r2_hidden(X52,X50)|X50!=k4_enumset1(X44,X45,X46,X47,X48,X49)))&(X52!=X48|r2_hidden(X52,X50)|X50!=k4_enumset1(X44,X45,X46,X47,X48,X49)))&(X52!=X49|r2_hidden(X52,X50)|X50!=k4_enumset1(X44,X45,X46,X47,X48,X49))))&(((((((esk1_7(X53,X54,X55,X56,X57,X58,X59)!=X53|~r2_hidden(esk1_7(X53,X54,X55,X56,X57,X58,X59),X59)|X59=k4_enumset1(X53,X54,X55,X56,X57,X58))&(esk1_7(X53,X54,X55,X56,X57,X58,X59)!=X54|~r2_hidden(esk1_7(X53,X54,X55,X56,X57,X58,X59),X59)|X59=k4_enumset1(X53,X54,X55,X56,X57,X58)))&(esk1_7(X53,X54,X55,X56,X57,X58,X59)!=X55|~r2_hidden(esk1_7(X53,X54,X55,X56,X57,X58,X59),X59)|X59=k4_enumset1(X53,X54,X55,X56,X57,X58)))&(esk1_7(X53,X54,X55,X56,X57,X58,X59)!=X56|~r2_hidden(esk1_7(X53,X54,X55,X56,X57,X58,X59),X59)|X59=k4_enumset1(X53,X54,X55,X56,X57,X58)))&(esk1_7(X53,X54,X55,X56,X57,X58,X59)!=X57|~r2_hidden(esk1_7(X53,X54,X55,X56,X57,X58,X59),X59)|X59=k4_enumset1(X53,X54,X55,X56,X57,X58)))&(esk1_7(X53,X54,X55,X56,X57,X58,X59)!=X58|~r2_hidden(esk1_7(X53,X54,X55,X56,X57,X58,X59),X59)|X59=k4_enumset1(X53,X54,X55,X56,X57,X58)))&(r2_hidden(esk1_7(X53,X54,X55,X56,X57,X58,X59),X59)|(esk1_7(X53,X54,X55,X56,X57,X58,X59)=X53|esk1_7(X53,X54,X55,X56,X57,X58,X59)=X54|esk1_7(X53,X54,X55,X56,X57,X58,X59)=X55|esk1_7(X53,X54,X55,X56,X57,X58,X59)=X56|esk1_7(X53,X54,X55,X56,X57,X58,X59)=X57|esk1_7(X53,X54,X55,X56,X57,X58,X59)=X58)|X59=k4_enumset1(X53,X54,X55,X56,X57,X58)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).
% 0.19/0.43  cnf(c_0_73, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.43  fof(c_0_74, plain, ![X67, X68]:((~v4_relat_1(X68,X67)|r1_tarski(k1_relat_1(X68),X67)|~v1_relat_1(X68))&(~r1_tarski(k1_relat_1(X68),X67)|v4_relat_1(X68,X67)|~v1_relat_1(X68))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.19/0.43  cnf(c_0_75, negated_conjecture, (~r2_hidden(esk2_0,k1_relat_1(esk5_0))|~r1_tarski(k7_relset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,esk4_0),k11_relat_1(esk5_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64])])).
% 0.19/0.43  cnf(c_0_76, negated_conjecture, (k7_relset_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,X1)=k9_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_65, c_0_52])).
% 0.19/0.43  cnf(c_0_77, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.19/0.43  cnf(c_0_78, negated_conjecture, (k9_relat_1(esk5_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))=k2_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_64])])).
% 0.19/0.43  cnf(c_0_79, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.43  cnf(c_0_80, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))|~r1_tarski(k1_relat_1(esk5_0),X1)), inference(spm,[status(thm)],[c_0_70, c_0_52])).
% 0.19/0.43  cnf(c_0_81, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.43  cnf(c_0_82, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X2,X4,X5,X6,X7,X8)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.43  cnf(c_0_83, plain, (X1=k1_xboole_0|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44])).
% 0.19/0.43  cnf(c_0_84, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.19/0.43  cnf(c_0_85, negated_conjecture, (~r2_hidden(esk2_0,k1_relat_1(esk5_0))|~r1_tarski(k9_relat_1(esk5_0,esk4_0),k11_relat_1(esk5_0,esk2_0))), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.43  cnf(c_0_86, negated_conjecture, (k11_relat_1(esk5_0,esk2_0)=k2_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_64])])).
% 0.19/0.43  fof(c_0_87, plain, ![X71, X72]:(~v1_relat_1(X72)|r1_tarski(k9_relat_1(X72,X71),k2_relat_1(X72))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).
% 0.19/0.43  cnf(c_0_88, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(X1,esk3_0))|~r1_tarski(k1_relat_1(esk5_0),X1)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.19/0.43  cnf(c_0_89, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_81])).
% 0.19/0.43  cnf(c_0_90, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X2,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_43]), c_0_44])).
% 0.19/0.43  cnf(c_0_91, plain, (k1_relat_1(X1)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|k1_relat_1(X1)=k1_xboole_0|~v4_relat_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.19/0.43  cnf(c_0_92, negated_conjecture, (~r2_hidden(esk2_0,k1_relat_1(esk5_0))|~r1_tarski(k9_relat_1(esk5_0,esk4_0),k2_relat_1(esk5_0))), inference(rw,[status(thm)],[c_0_85, c_0_86])).
% 0.19/0.43  cnf(c_0_93, plain, (r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.19/0.43  fof(c_0_94, plain, ![X42, X43]:((k2_zfmisc_1(X42,X43)!=k1_xboole_0|(X42=k1_xboole_0|X43=k1_xboole_0))&((X42!=k1_xboole_0|k2_zfmisc_1(X42,X43)=k1_xboole_0)&(X43!=k1_xboole_0|k2_zfmisc_1(X42,X43)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.43  cnf(c_0_95, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.43  cnf(c_0_96, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(k1_relat_1(esk5_0),esk3_0))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.19/0.43  cnf(c_0_97, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_90])])).
% 0.19/0.43  cnf(c_0_98, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=k1_relat_1(esk5_0)|k1_relat_1(esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_68]), c_0_64])])).
% 0.19/0.43  cnf(c_0_99, negated_conjecture, (~r2_hidden(esk2_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_64])])).
% 0.19/0.43  cnf(c_0_100, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.19/0.43  fof(c_0_101, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.43  cnf(c_0_102, negated_conjecture, (k2_zfmisc_1(k1_relat_1(esk5_0),esk3_0)=esk5_0|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk5_0),esk3_0),esk5_0)), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.19/0.43  cnf(c_0_103, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])).
% 0.19/0.43  cnf(c_0_104, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_100])).
% 0.19/0.43  cnf(c_0_105, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.19/0.43  fof(c_0_106, plain, ![X75]:k9_relat_1(k1_xboole_0,X75)=k1_xboole_0, inference(variable_rename,[status(thm)],[t150_relat_1])).
% 0.19/0.43  cnf(c_0_107, negated_conjecture, (~r1_tarski(k9_relat_1(esk5_0,esk4_0),k6_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0)))), inference(rw,[status(thm)],[c_0_61, c_0_76])).
% 0.19/0.43  cnf(c_0_108, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_103]), c_0_104]), c_0_103]), c_0_104]), c_0_105])])).
% 0.19/0.43  cnf(c_0_109, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.19/0.43  cnf(c_0_110, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_108]), c_0_109]), c_0_108]), c_0_108]), c_0_108]), c_0_108]), c_0_108]), c_0_108]), c_0_108]), c_0_108]), c_0_105])]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 111
% 0.19/0.43  # Proof object clause steps            : 58
% 0.19/0.43  # Proof object formula steps           : 53
% 0.19/0.43  # Proof object conjectures             : 26
% 0.19/0.43  # Proof object clause conjectures      : 23
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 29
% 0.19/0.43  # Proof object initial formulas used   : 26
% 0.19/0.43  # Proof object generating inferences   : 15
% 0.19/0.43  # Proof object simplifying inferences  : 90
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 26
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 52
% 0.19/0.43  # Removed in clause preprocessing      : 7
% 0.19/0.43  # Initial clauses in saturation        : 45
% 0.19/0.43  # Processed clauses                    : 411
% 0.19/0.43  # ...of these trivial                  : 2
% 0.19/0.43  # ...subsumed                          : 145
% 0.19/0.43  # ...remaining for further processing  : 264
% 0.19/0.43  # Other redundant clauses eliminated   : 25
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 13
% 0.19/0.43  # Backward-rewritten                   : 110
% 0.19/0.43  # Generated clauses                    : 748
% 0.19/0.43  # ...of the previous two non-trivial   : 678
% 0.19/0.43  # Contextual simplify-reflections      : 5
% 0.19/0.43  # Paramodulations                      : 729
% 0.19/0.43  # Factorizations                       : 0
% 0.19/0.43  # Equation resolutions                 : 25
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 86
% 0.19/0.43  #    Positive orientable unit clauses  : 24
% 0.19/0.43  #    Positive unorientable unit clauses: 1
% 0.19/0.43  #    Negative unit clauses             : 1
% 0.19/0.43  #    Non-unit-clauses                  : 60
% 0.19/0.43  # Current number of unprocessed clauses: 318
% 0.19/0.43  # ...number of literals in the above   : 2862
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 172
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 14645
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 2289
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 139
% 0.19/0.43  # Unit Clause-clause subsumption calls : 317
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 57
% 0.19/0.43  # BW rewrite match successes           : 7
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 40742
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.101 s
% 0.19/0.44  # System time              : 0.003 s
% 0.19/0.44  # Total time               : 0.104 s
% 0.19/0.44  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
