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
% DateTime   : Thu Dec  3 11:13:27 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 334 expanded)
%              Number of clauses        :   60 ( 143 expanded)
%              Number of leaves         :   21 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :  252 (1244 expanded)
%              Number of equality atoms :   91 ( 433 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_tops_2,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_struct_0(X2) = k1_xboole_0
                 => k2_struct_0(X1) = k1_xboole_0 )
               => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_struct_0(X2)) = k2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(t132_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | v1_partfun1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(fc17_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ( v1_xboole_0(k7_relat_1(X1,X2))
        & v1_relat_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

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

fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(t162_funct_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k9_relat_1(k6_relat_1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( l1_struct_0(X2)
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( ( k2_struct_0(X2) = k1_xboole_0
                   => k2_struct_0(X1) = k1_xboole_0 )
                 => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_struct_0(X2)) = k2_struct_0(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_tops_2])).

fof(c_0_22,plain,(
    ! [X34,X35,X36] :
      ( ( v4_relat_1(X36,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( v5_relat_1(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_23,negated_conjecture,
    ( l1_struct_0(esk2_0)
    & l1_struct_0(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
    & ( k2_struct_0(esk3_0) != k1_xboole_0
      | k2_struct_0(esk2_0) = k1_xboole_0 )
    & k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,k2_struct_0(esk3_0)) != k2_struct_0(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_24,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | v1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_25,plain,(
    ! [X53] :
      ( ~ l1_struct_0(X53)
      | k2_struct_0(X53) = u1_struct_0(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_26,plain,(
    ! [X13,X14] :
      ( ( ~ v5_relat_1(X14,X13)
        | r1_tarski(k2_relat_1(X14),X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r1_tarski(k2_relat_1(X14),X13)
        | v5_relat_1(X14,X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_27,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X50,X51,X52] :
      ( ( X51 = k1_xboole_0
        | v1_partfun1(X52,X50)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
        | ~ v1_funct_1(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( X50 != k1_xboole_0
        | v1_partfun1(X52,X50)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
        | ~ v1_funct_1(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).

fof(c_0_31,plain,(
    ! [X8,X9] :
      ( ~ v1_xboole_0(X8)
      | X8 = X9
      | ~ v1_xboole_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_32,plain,(
    ! [X16,X17] :
      ( ( v1_xboole_0(k7_relat_1(X16,X17))
        | ~ v1_xboole_0(X16)
        | ~ v1_relat_1(X16) )
      & ( v1_relat_1(k7_relat_1(X16,X17))
        | ~ v1_xboole_0(X16)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc17_relat_1])])])).

fof(c_0_33,plain,(
    ! [X12] :
      ( ~ v1_xboole_0(X12)
      | v1_relat_1(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_34,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_37,plain,(
    ! [X37,X38,X39,X40] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k8_relset_1(X37,X38,X39,X40) = k10_relat_1(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_38,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | k1_relat_1(k5_relat_1(X20,X21)) = k10_relat_1(X20,k1_relat_1(X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_39,plain,(
    ! [X24] :
      ( k1_relat_1(k6_relat_1(X24)) = X24
      & k2_relat_1(k6_relat_1(X24)) = X24 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_40,plain,(
    ! [X15] : v1_relat_1(k6_relat_1(X15)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_41,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X26)
      | ~ r1_tarski(k2_relat_1(X26),X25)
      | k5_relat_1(X26,k6_relat_1(X25)) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

cnf(c_0_42,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_43,negated_conjecture,
    ( v5_relat_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_47,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_48,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_49,plain,
    ( v1_xboole_0(k7_relat_1(X1,X2))
    | ~ v1_xboole_0(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_50,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,k2_struct_0(esk3_0)) != k2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_52,negated_conjecture,
    ( k2_struct_0(esk3_0) = u1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_53,negated_conjecture,
    ( k2_struct_0(esk2_0) = u1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_54,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_55,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_56,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_57,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_58,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

fof(c_0_60,plain,(
    ! [X48,X49] :
      ( ( ~ v1_partfun1(X49,X48)
        | k1_relat_1(X49) = X48
        | ~ v1_relat_1(X49)
        | ~ v4_relat_1(X49,X48) )
      & ( k1_relat_1(X49) != X48
        | v1_partfun1(X49,X48)
        | ~ v1_relat_1(X49)
        | ~ v4_relat_1(X49,X48) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_45])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_64,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_65,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | k9_relat_1(k6_relat_1(X27),X28) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_funct_1])])).

fof(c_0_66,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | k2_relat_1(k7_relat_1(X19,X18)) = k9_relat_1(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_46]),c_0_48])])).

cnf(c_0_68,plain,
    ( v1_xboole_0(k7_relat_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_69,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,u1_struct_0(esk3_0)) != u1_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_70,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1) = k10_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_28])).

cnf(c_0_71,plain,
    ( k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_72,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(u1_struct_0(esk3_0))) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_44])])).

cnf(c_0_73,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v1_partfun1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_28]),c_0_62]),c_0_63])])).

cnf(c_0_75,negated_conjecture,
    ( v4_relat_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_28])).

cnf(c_0_76,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_xboole_0(k6_relat_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_47])).

cnf(c_0_77,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_78,negated_conjecture,
    ( k2_struct_0(esk2_0) = k1_xboole_0
    | k2_struct_0(esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_79,plain,
    ( k9_relat_1(k6_relat_1(X2),X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_80,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_81,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_82,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_83,negated_conjecture,
    ( k10_relat_1(esk4_0,u1_struct_0(esk3_0)) != u1_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_84,negated_conjecture,
    ( k10_relat_1(esk4_0,u1_struct_0(esk3_0)) = k1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_44])])).

fof(c_0_85,plain,(
    ! [X10,X11] :
      ( ( k2_zfmisc_1(X10,X11) != k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_86,negated_conjecture,
    ( k1_relat_1(esk4_0) = u1_struct_0(esk2_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_44])])).

cnf(c_0_87,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_48])])).

cnf(c_0_88,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | u1_struct_0(esk3_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_52]),c_0_53])).

cnf(c_0_89,negated_conjecture,
    ( k9_relat_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))),esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_28])).

cnf(c_0_90,plain,
    ( k9_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_50])).

cnf(c_0_91,negated_conjecture,
    ( k1_relat_1(esk4_0) != u1_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_92,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | ~ v1_xboole_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ v1_xboole_0(k6_relat_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_86,c_0_91])).

cnf(c_0_96,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_92])).

cnf(c_0_97,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_87]),c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95]),c_0_96]),c_0_77]),c_0_48])])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n021.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 13:31:19 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.34  # No SInE strategy applied
% 0.11/0.34  # Trying AutoSched0 for 299 seconds
% 0.11/0.38  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.11/0.38  # and selection function SelectNewComplexAHPNS.
% 0.11/0.38  #
% 0.11/0.38  # Preprocessing time       : 0.028 s
% 0.11/0.38  # Presaturation interreduction done
% 0.11/0.38  
% 0.11/0.38  # Proof found!
% 0.11/0.38  # SZS status Theorem
% 0.11/0.38  # SZS output start CNFRefutation
% 0.11/0.38  fof(t52_tops_2, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_struct_0(X2)=k1_xboole_0=>k2_struct_0(X1)=k1_xboole_0)=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_struct_0(X2))=k2_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 0.11/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.11/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.11/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.11/0.38  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.11/0.38  fof(t132_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 0.11/0.38  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.11/0.38  fof(fc17_relat_1, axiom, ![X1, X2]:((v1_xboole_0(X1)&v1_relat_1(X1))=>(v1_xboole_0(k7_relat_1(X1,X2))&v1_relat_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc17_relat_1)).
% 0.11/0.38  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.11/0.38  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.11/0.38  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.11/0.38  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.11/0.38  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.11/0.38  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 0.11/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.11/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.11/0.38  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.11/0.38  fof(t162_funct_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k9_relat_1(k6_relat_1(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 0.11/0.38  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.11/0.38  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 0.11/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.11/0.38  fof(c_0_21, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_struct_0(X2)=k1_xboole_0=>k2_struct_0(X1)=k1_xboole_0)=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_struct_0(X2))=k2_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t52_tops_2])).
% 0.11/0.38  fof(c_0_22, plain, ![X34, X35, X36]:((v4_relat_1(X36,X34)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(v5_relat_1(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.11/0.38  fof(c_0_23, negated_conjecture, (l1_struct_0(esk2_0)&(l1_struct_0(esk3_0)&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))))&((k2_struct_0(esk3_0)!=k1_xboole_0|k2_struct_0(esk2_0)=k1_xboole_0)&k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,k2_struct_0(esk3_0))!=k2_struct_0(esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.11/0.38  fof(c_0_24, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|v1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.11/0.38  fof(c_0_25, plain, ![X53]:(~l1_struct_0(X53)|k2_struct_0(X53)=u1_struct_0(X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.11/0.38  fof(c_0_26, plain, ![X13, X14]:((~v5_relat_1(X14,X13)|r1_tarski(k2_relat_1(X14),X13)|~v1_relat_1(X14))&(~r1_tarski(k2_relat_1(X14),X13)|v5_relat_1(X14,X13)|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.11/0.38  cnf(c_0_27, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.11/0.38  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.11/0.38  cnf(c_0_29, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.11/0.38  fof(c_0_30, plain, ![X50, X51, X52]:((X51=k1_xboole_0|v1_partfun1(X52,X50)|(~v1_funct_1(X52)|~v1_funct_2(X52,X50,X51)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))|(~v1_funct_1(X52)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))))&(X50!=k1_xboole_0|v1_partfun1(X52,X50)|(~v1_funct_1(X52)|~v1_funct_2(X52,X50,X51)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))|(~v1_funct_1(X52)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).
% 0.11/0.38  fof(c_0_31, plain, ![X8, X9]:(~v1_xboole_0(X8)|X8=X9|~v1_xboole_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.11/0.38  fof(c_0_32, plain, ![X16, X17]:((v1_xboole_0(k7_relat_1(X16,X17))|(~v1_xboole_0(X16)|~v1_relat_1(X16)))&(v1_relat_1(k7_relat_1(X16,X17))|(~v1_xboole_0(X16)|~v1_relat_1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc17_relat_1])])])).
% 0.11/0.38  fof(c_0_33, plain, ![X12]:(~v1_xboole_0(X12)|v1_relat_1(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.11/0.38  cnf(c_0_34, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.11/0.38  cnf(c_0_35, negated_conjecture, (l1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.11/0.38  cnf(c_0_36, negated_conjecture, (l1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.11/0.38  fof(c_0_37, plain, ![X37, X38, X39, X40]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k8_relset_1(X37,X38,X39,X40)=k10_relat_1(X39,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.11/0.38  fof(c_0_38, plain, ![X20, X21]:(~v1_relat_1(X20)|(~v1_relat_1(X21)|k1_relat_1(k5_relat_1(X20,X21))=k10_relat_1(X20,k1_relat_1(X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.11/0.38  fof(c_0_39, plain, ![X24]:(k1_relat_1(k6_relat_1(X24))=X24&k2_relat_1(k6_relat_1(X24))=X24), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.11/0.38  fof(c_0_40, plain, ![X15]:v1_relat_1(k6_relat_1(X15)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.11/0.38  fof(c_0_41, plain, ![X25, X26]:(~v1_relat_1(X26)|(~r1_tarski(k2_relat_1(X26),X25)|k5_relat_1(X26,k6_relat_1(X25))=X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 0.11/0.38  cnf(c_0_42, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.11/0.38  cnf(c_0_43, negated_conjecture, (v5_relat_1(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.11/0.38  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.11/0.38  cnf(c_0_45, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.11/0.38  cnf(c_0_46, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.11/0.38  cnf(c_0_47, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.11/0.38  cnf(c_0_48, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.11/0.38  cnf(c_0_49, plain, (v1_xboole_0(k7_relat_1(X1,X2))|~v1_xboole_0(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.11/0.38  cnf(c_0_50, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.11/0.38  cnf(c_0_51, negated_conjecture, (k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,k2_struct_0(esk3_0))!=k2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.11/0.38  cnf(c_0_52, negated_conjecture, (k2_struct_0(esk3_0)=u1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.11/0.38  cnf(c_0_53, negated_conjecture, (k2_struct_0(esk2_0)=u1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_34, c_0_36])).
% 0.11/0.38  cnf(c_0_54, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.11/0.38  cnf(c_0_55, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.11/0.38  cnf(c_0_56, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.11/0.38  cnf(c_0_57, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.11/0.38  cnf(c_0_58, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.11/0.38  cnf(c_0_59, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.11/0.38  fof(c_0_60, plain, ![X48, X49]:((~v1_partfun1(X49,X48)|k1_relat_1(X49)=X48|(~v1_relat_1(X49)|~v4_relat_1(X49,X48)))&(k1_relat_1(X49)!=X48|v1_partfun1(X49,X48)|(~v1_relat_1(X49)|~v4_relat_1(X49,X48)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.11/0.38  cnf(c_0_61, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(cn,[status(thm)],[c_0_45])).
% 0.11/0.38  cnf(c_0_62, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.11/0.38  cnf(c_0_63, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.11/0.38  cnf(c_0_64, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.11/0.38  fof(c_0_65, plain, ![X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(X27))|k9_relat_1(k6_relat_1(X27),X28)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_funct_1])])).
% 0.11/0.38  fof(c_0_66, plain, ![X18, X19]:(~v1_relat_1(X19)|k2_relat_1(k7_relat_1(X19,X18))=k9_relat_1(X19,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.11/0.38  cnf(c_0_67, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_46]), c_0_48])])).
% 0.11/0.38  cnf(c_0_68, plain, (v1_xboole_0(k7_relat_1(X1,X2))|~v1_xboole_0(X1)), inference(csr,[status(thm)],[c_0_49, c_0_50])).
% 0.11/0.38  cnf(c_0_69, negated_conjecture, (k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,u1_struct_0(esk3_0))!=u1_struct_0(esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.11/0.38  cnf(c_0_70, negated_conjecture, (k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1)=k10_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_28])).
% 0.11/0.38  cnf(c_0_71, plain, (k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.11/0.38  cnf(c_0_72, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(u1_struct_0(esk3_0)))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_44])])).
% 0.11/0.38  cnf(c_0_73, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.11/0.38  cnf(c_0_74, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v1_partfun1(esk4_0,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_28]), c_0_62]), c_0_63])])).
% 0.11/0.38  cnf(c_0_75, negated_conjecture, (v4_relat_1(esk4_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_64, c_0_28])).
% 0.11/0.38  cnf(c_0_76, plain, (k1_relat_1(X1)=X2|~v1_xboole_0(k6_relat_1(X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_56, c_0_47])).
% 0.11/0.38  cnf(c_0_77, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.11/0.38  cnf(c_0_78, negated_conjecture, (k2_struct_0(esk2_0)=k1_xboole_0|k2_struct_0(esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.11/0.38  cnf(c_0_79, plain, (k9_relat_1(k6_relat_1(X2),X1)=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.11/0.38  cnf(c_0_80, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.11/0.39  cnf(c_0_81, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.11/0.39  cnf(c_0_82, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.11/0.39  cnf(c_0_83, negated_conjecture, (k10_relat_1(esk4_0,u1_struct_0(esk3_0))!=u1_struct_0(esk2_0)), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.11/0.39  cnf(c_0_84, negated_conjecture, (k10_relat_1(esk4_0,u1_struct_0(esk3_0))=k1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_44])])).
% 0.11/0.39  fof(c_0_85, plain, ![X10, X11]:((k2_zfmisc_1(X10,X11)!=k1_xboole_0|(X10=k1_xboole_0|X11=k1_xboole_0))&((X10!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0)&(X11!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.11/0.39  cnf(c_0_86, negated_conjecture, (k1_relat_1(esk4_0)=u1_struct_0(esk2_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_44])])).
% 0.11/0.39  cnf(c_0_87, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_48])])).
% 0.11/0.39  cnf(c_0_88, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|u1_struct_0(esk3_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_52]), c_0_53])).
% 0.11/0.39  cnf(c_0_89, negated_conjecture, (k9_relat_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))),esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_79, c_0_28])).
% 0.11/0.39  cnf(c_0_90, plain, (k9_relat_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_50])).
% 0.11/0.39  cnf(c_0_91, negated_conjecture, (k1_relat_1(esk4_0)!=u1_struct_0(esk2_0)), inference(rw,[status(thm)],[c_0_83, c_0_84])).
% 0.11/0.39  cnf(c_0_92, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.11/0.39  cnf(c_0_93, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|~v1_xboole_0(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])).
% 0.11/0.39  cnf(c_0_94, negated_conjecture, (esk4_0=k1_xboole_0|~v1_xboole_0(k6_relat_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.11/0.39  cnf(c_0_95, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_86, c_0_91])).
% 0.11/0.39  cnf(c_0_96, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_92])).
% 0.11/0.39  cnf(c_0_97, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_87]), c_0_93])).
% 0.11/0.39  cnf(c_0_98, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95]), c_0_96]), c_0_77]), c_0_48])])).
% 0.11/0.39  cnf(c_0_99, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_98]), c_0_48])]), ['proof']).
% 0.11/0.39  # SZS output end CNFRefutation
% 0.11/0.39  # Proof object total steps             : 100
% 0.11/0.39  # Proof object clause steps            : 60
% 0.11/0.39  # Proof object formula steps           : 40
% 0.11/0.39  # Proof object conjectures             : 32
% 0.11/0.39  # Proof object clause conjectures      : 29
% 0.11/0.39  # Proof object formula conjectures     : 3
% 0.11/0.39  # Proof object initial clauses used    : 29
% 0.11/0.39  # Proof object initial formulas used   : 21
% 0.11/0.39  # Proof object generating inferences   : 21
% 0.11/0.39  # Proof object simplifying inferences  : 41
% 0.11/0.39  # Training examples: 0 positive, 0 negative
% 0.11/0.39  # Parsed axioms                        : 24
% 0.11/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.39  # Initial clauses                      : 40
% 0.11/0.39  # Removed in clause preprocessing      : 0
% 0.11/0.39  # Initial clauses in saturation        : 40
% 0.11/0.39  # Processed clauses                    : 366
% 0.11/0.39  # ...of these trivial                  : 3
% 0.11/0.39  # ...subsumed                          : 153
% 0.11/0.39  # ...remaining for further processing  : 210
% 0.11/0.39  # Other redundant clauses eliminated   : 18
% 0.11/0.39  # Clauses deleted for lack of memory   : 0
% 0.11/0.39  # Backward-subsumed                    : 5
% 0.11/0.39  # Backward-rewritten                   : 57
% 0.11/0.39  # Generated clauses                    : 623
% 0.11/0.39  # ...of the previous two non-trivial   : 618
% 0.11/0.39  # Contextual simplify-reflections      : 10
% 0.11/0.39  # Paramodulations                      : 604
% 0.11/0.39  # Factorizations                       : 0
% 0.11/0.39  # Equation resolutions                 : 18
% 0.11/0.39  # Propositional unsat checks           : 0
% 0.11/0.39  #    Propositional check models        : 0
% 0.11/0.39  #    Propositional check unsatisfiable : 0
% 0.11/0.39  #    Propositional clauses             : 0
% 0.11/0.39  #    Propositional clauses after purity: 0
% 0.11/0.39  #    Propositional unsat core size     : 0
% 0.11/0.39  #    Propositional preprocessing time  : 0.000
% 0.11/0.39  #    Propositional encoding time       : 0.000
% 0.11/0.39  #    Propositional solver time         : 0.000
% 0.11/0.39  #    Success case prop preproc time    : 0.000
% 0.11/0.39  #    Success case prop encoding time   : 0.000
% 0.11/0.39  #    Success case prop solver time     : 0.000
% 0.11/0.39  # Current number of processed clauses  : 103
% 0.11/0.39  #    Positive orientable unit clauses  : 22
% 0.11/0.39  #    Positive unorientable unit clauses: 0
% 0.11/0.39  #    Negative unit clauses             : 0
% 0.11/0.39  #    Non-unit-clauses                  : 81
% 0.11/0.39  # Current number of unprocessed clauses: 319
% 0.11/0.39  # ...number of literals in the above   : 1324
% 0.11/0.39  # Current number of archived formulas  : 0
% 0.11/0.39  # Current number of archived clauses   : 103
% 0.11/0.39  # Clause-clause subsumption calls (NU) : 3143
% 0.11/0.39  # Rec. Clause-clause subsumption calls : 2146
% 0.11/0.39  # Non-unit clause-clause subsumptions  : 168
% 0.11/0.39  # Unit Clause-clause subsumption calls : 150
% 0.11/0.39  # Rewrite failures with RHS unbound    : 0
% 0.11/0.39  # BW rewrite match attempts            : 8
% 0.11/0.39  # BW rewrite match successes           : 7
% 0.11/0.39  # Condensation attempts                : 0
% 0.11/0.39  # Condensation successes               : 0
% 0.11/0.39  # Termbank termtop insertions          : 9501
% 0.11/0.39  
% 0.11/0.39  # -------------------------------------------------
% 0.11/0.39  # User time                : 0.045 s
% 0.11/0.39  # System time              : 0.008 s
% 0.11/0.39  # Total time               : 0.053 s
% 0.11/0.39  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
