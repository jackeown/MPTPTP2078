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
% DateTime   : Thu Dec  3 10:57:52 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 (  85 expanded)
%              Number of clauses        :   33 (  39 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  138 ( 184 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t35_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => m1_subset_1(k6_relset_1(X3,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

fof(t116_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(l29_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k8_relat_1(X1,X2)),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_wellord1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(redefinition_k6_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k6_relset_1(X1,X2,X3,X4) = k8_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(c_0_13,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X10,X9)
        | r1_tarski(X10,X8)
        | X9 != k1_zfmisc_1(X8) )
      & ( ~ r1_tarski(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k1_zfmisc_1(X8) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | ~ r1_tarski(esk1_2(X12,X13),X12)
        | X13 = k1_zfmisc_1(X12) )
      & ( r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(esk1_2(X12,X13),X12)
        | X13 = k1_zfmisc_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_14,plain,(
    ! [X15] : ~ v1_xboole_0(k1_zfmisc_1(X15)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_15,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X16,X17)
      | v1_xboole_0(X17)
      | r2_hidden(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
       => m1_subset_1(k6_relset_1(X3,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ),
    inference(assume_negation,[status(cth)],[t35_relset_1])).

fof(c_0_20,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | r1_tarski(k2_relat_1(k8_relat_1(X20,X21)),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).

fof(c_0_21,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | v1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_22,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_25,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | m1_subset_1(k1_relset_1(X27,X28,X29),k1_zfmisc_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

fof(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))
    & ~ m1_subset_1(k6_relset_1(esk4_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_27,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | r1_tarski(k1_relat_1(k8_relat_1(X22,X23)),k1_relat_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l29_wellord1])])).

fof(c_0_28,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k1_relset_1(X30,X31,X32) = k1_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_29,plain,(
    ! [X37,X38,X39] :
      ( ~ v1_relat_1(X39)
      | ~ r1_tarski(k1_relat_1(X39),X37)
      | ~ r1_tarski(k2_relat_1(X39),X38)
      | m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X2,X1)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_40,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | v1_relat_1(k8_relat_1(X18,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k1_relset_1(esk4_0,esk2_0,esk5_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X1,X2)),k1_relat_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_relset_1(esk4_0,esk2_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_35])).

cnf(c_0_45,plain,
    ( m1_subset_1(k8_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_relat_1(k8_relat_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ r1_tarski(k1_relat_1(k8_relat_1(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,k1_relset_1(esk4_0,esk2_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k1_relat_1(k8_relat_1(X1,esk5_0)),k1_relset_1(esk4_0,esk2_0,esk5_0))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_49,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k6_relset_1(X33,X34,X35,X36) = k8_relat_1(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_relset_1])])).

cnf(c_0_50,plain,
    ( m1_subset_1(k8_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ r1_tarski(k1_relat_1(k8_relat_1(X1,X2)),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_31])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k1_relat_1(k8_relat_1(X1,esk5_0)),esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( k6_relset_1(X2,X3,X4,X1) = k8_relat_1(X4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k8_relat_1(X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( ~ m1_subset_1(k6_relset_1(esk4_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_55,negated_conjecture,
    ( k6_relset_1(esk4_0,esk2_0,X1,esk5_0) = k8_relat_1(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k8_relat_1(X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_35])).

cnf(c_0_57,negated_conjecture,
    ( ~ m1_subset_1(k8_relat_1(esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k8_relat_1(X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_35])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:04:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.50  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.20/0.50  # and selection function SelectVGNonCR.
% 0.20/0.50  #
% 0.20/0.50  # Preprocessing time       : 0.027 s
% 0.20/0.50  # Presaturation interreduction done
% 0.20/0.50  
% 0.20/0.50  # Proof found!
% 0.20/0.50  # SZS status Theorem
% 0.20/0.50  # SZS output start CNFRefutation
% 0.20/0.50  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.50  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.20/0.50  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.50  fof(t35_relset_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>m1_subset_1(k6_relset_1(X3,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 0.20/0.50  fof(t116_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 0.20/0.50  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.50  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.50  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.20/0.50  fof(l29_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k8_relat_1(X1,X2)),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_wellord1)).
% 0.20/0.50  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.50  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.20/0.50  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.20/0.50  fof(redefinition_k6_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k6_relset_1(X1,X2,X3,X4)=k8_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 0.20/0.50  fof(c_0_13, plain, ![X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X10,X9)|r1_tarski(X10,X8)|X9!=k1_zfmisc_1(X8))&(~r1_tarski(X11,X8)|r2_hidden(X11,X9)|X9!=k1_zfmisc_1(X8)))&((~r2_hidden(esk1_2(X12,X13),X13)|~r1_tarski(esk1_2(X12,X13),X12)|X13=k1_zfmisc_1(X12))&(r2_hidden(esk1_2(X12,X13),X13)|r1_tarski(esk1_2(X12,X13),X12)|X13=k1_zfmisc_1(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.50  fof(c_0_14, plain, ![X15]:~v1_xboole_0(k1_zfmisc_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.20/0.50  fof(c_0_15, plain, ![X16, X17]:(~m1_subset_1(X16,X17)|(v1_xboole_0(X17)|r2_hidden(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.50  cnf(c_0_16, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.50  cnf(c_0_17, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.50  cnf(c_0_18, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.50  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>m1_subset_1(k6_relset_1(X3,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X2))))), inference(assume_negation,[status(cth)],[t35_relset_1])).
% 0.20/0.50  fof(c_0_20, plain, ![X20, X21]:(~v1_relat_1(X21)|r1_tarski(k2_relat_1(k8_relat_1(X20,X21)),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).
% 0.20/0.50  fof(c_0_21, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|v1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.50  fof(c_0_22, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.50  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_16])).
% 0.20/0.50  cnf(c_0_24, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.50  fof(c_0_25, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|m1_subset_1(k1_relset_1(X27,X28,X29),k1_zfmisc_1(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.20/0.50  fof(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))&~m1_subset_1(k6_relset_1(esk4_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.20/0.50  fof(c_0_27, plain, ![X22, X23]:(~v1_relat_1(X23)|r1_tarski(k1_relat_1(k8_relat_1(X22,X23)),k1_relat_1(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l29_wellord1])])).
% 0.20/0.50  fof(c_0_28, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|k1_relset_1(X30,X31,X32)=k1_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.50  fof(c_0_29, plain, ![X37, X38, X39]:(~v1_relat_1(X39)|(~r1_tarski(k1_relat_1(X39),X37)|~r1_tarski(k2_relat_1(X39),X38)|m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.20/0.51  cnf(c_0_30, plain, (r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.51  cnf(c_0_31, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.51  cnf(c_0_32, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.51  cnf(c_0_34, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.51  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.51  cnf(c_0_36, plain, (r1_tarski(k1_relat_1(k8_relat_1(X2,X1)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.51  cnf(c_0_37, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.51  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.51  cnf(c_0_39, plain, (r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.51  fof(c_0_40, plain, ![X18, X19]:(~v1_relat_1(X19)|v1_relat_1(k8_relat_1(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.20/0.51  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.51  cnf(c_0_42, negated_conjecture, (m1_subset_1(k1_relset_1(esk4_0,esk2_0,esk5_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.51  cnf(c_0_43, plain, (r1_tarski(k1_relat_1(k8_relat_1(X1,X2)),k1_relat_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(spm,[status(thm)],[c_0_36, c_0_31])).
% 0.20/0.51  cnf(c_0_44, negated_conjecture, (k1_relat_1(esk5_0)=k1_relset_1(esk4_0,esk2_0,esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_35])).
% 0.20/0.51  cnf(c_0_45, plain, (m1_subset_1(k8_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_relat_1(k8_relat_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))|~r1_tarski(k1_relat_1(k8_relat_1(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.51  cnf(c_0_46, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.51  cnf(c_0_47, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,k1_relset_1(esk4_0,esk2_0,esk5_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.51  cnf(c_0_48, negated_conjecture, (r1_tarski(k1_relat_1(k8_relat_1(X1,esk5_0)),k1_relset_1(esk4_0,esk2_0,esk5_0))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.51  fof(c_0_49, plain, ![X33, X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k6_relset_1(X33,X34,X35,X36)=k8_relat_1(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_relset_1])])).
% 0.20/0.51  cnf(c_0_50, plain, (m1_subset_1(k8_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))|~r1_tarski(k1_relat_1(k8_relat_1(X1,X2)),X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_31])).
% 0.20/0.51  cnf(c_0_51, negated_conjecture, (r1_tarski(k1_relat_1(k8_relat_1(X1,esk5_0)),esk4_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.51  cnf(c_0_52, plain, (k6_relset_1(X2,X3,X4,X1)=k8_relat_1(X4,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.51  cnf(c_0_53, negated_conjecture, (m1_subset_1(k8_relat_1(X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.51  cnf(c_0_54, negated_conjecture, (~m1_subset_1(k6_relset_1(esk4_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.51  cnf(c_0_55, negated_conjecture, (k6_relset_1(esk4_0,esk2_0,X1,esk5_0)=k8_relat_1(X1,esk5_0)), inference(spm,[status(thm)],[c_0_52, c_0_35])).
% 0.20/0.51  cnf(c_0_56, negated_conjecture, (m1_subset_1(k8_relat_1(X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_53, c_0_35])).
% 0.20/0.51  cnf(c_0_57, negated_conjecture, (~m1_subset_1(k8_relat_1(esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.51  cnf(c_0_58, negated_conjecture, (m1_subset_1(k8_relat_1(X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_56, c_0_35])).
% 0.20/0.51  cnf(c_0_59, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])]), ['proof']).
% 0.20/0.51  # SZS output end CNFRefutation
% 0.20/0.51  # Proof object total steps             : 60
% 0.20/0.51  # Proof object clause steps            : 33
% 0.20/0.51  # Proof object formula steps           : 27
% 0.20/0.51  # Proof object conjectures             : 16
% 0.20/0.51  # Proof object clause conjectures      : 13
% 0.20/0.51  # Proof object formula conjectures     : 3
% 0.20/0.51  # Proof object initial clauses used    : 14
% 0.20/0.51  # Proof object initial formulas used   : 13
% 0.20/0.51  # Proof object generating inferences   : 17
% 0.20/0.51  # Proof object simplifying inferences  : 4
% 0.20/0.51  # Training examples: 0 positive, 0 negative
% 0.20/0.51  # Parsed axioms                        : 13
% 0.20/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.51  # Initial clauses                      : 17
% 0.20/0.51  # Removed in clause preprocessing      : 0
% 0.20/0.51  # Initial clauses in saturation        : 17
% 0.20/0.51  # Processed clauses                    : 678
% 0.20/0.51  # ...of these trivial                  : 0
% 0.20/0.51  # ...subsumed                          : 141
% 0.20/0.51  # ...remaining for further processing  : 537
% 0.20/0.51  # Other redundant clauses eliminated   : 0
% 0.20/0.51  # Clauses deleted for lack of memory   : 0
% 0.20/0.51  # Backward-subsumed                    : 26
% 0.20/0.51  # Backward-rewritten                   : 4
% 0.20/0.51  # Generated clauses                    : 5930
% 0.20/0.51  # ...of the previous two non-trivial   : 5895
% 0.20/0.51  # Contextual simplify-reflections      : 7
% 0.20/0.51  # Paramodulations                      : 5905
% 0.20/0.51  # Factorizations                       : 22
% 0.20/0.51  # Equation resolutions                 : 3
% 0.20/0.51  # Propositional unsat checks           : 0
% 0.20/0.51  #    Propositional check models        : 0
% 0.20/0.51  #    Propositional check unsatisfiable : 0
% 0.20/0.51  #    Propositional clauses             : 0
% 0.20/0.51  #    Propositional clauses after purity: 0
% 0.20/0.51  #    Propositional unsat core size     : 0
% 0.20/0.51  #    Propositional preprocessing time  : 0.000
% 0.20/0.51  #    Propositional encoding time       : 0.000
% 0.20/0.51  #    Propositional solver time         : 0.000
% 0.20/0.51  #    Success case prop preproc time    : 0.000
% 0.20/0.51  #    Success case prop encoding time   : 0.000
% 0.20/0.51  #    Success case prop solver time     : 0.000
% 0.20/0.51  # Current number of processed clauses  : 490
% 0.20/0.51  #    Positive orientable unit clauses  : 5
% 0.20/0.51  #    Positive unorientable unit clauses: 0
% 0.20/0.51  #    Negative unit clauses             : 1
% 0.20/0.51  #    Non-unit-clauses                  : 484
% 0.20/0.51  # Current number of unprocessed clauses: 5249
% 0.20/0.51  # ...number of literals in the above   : 18413
% 0.20/0.51  # Current number of archived formulas  : 0
% 0.20/0.51  # Current number of archived clauses   : 47
% 0.20/0.51  # Clause-clause subsumption calls (NU) : 42382
% 0.20/0.51  # Rec. Clause-clause subsumption calls : 25404
% 0.20/0.51  # Non-unit clause-clause subsumptions  : 174
% 0.20/0.51  # Unit Clause-clause subsumption calls : 22
% 0.20/0.51  # Rewrite failures with RHS unbound    : 0
% 0.20/0.51  # BW rewrite match attempts            : 13
% 0.20/0.51  # BW rewrite match successes           : 3
% 0.20/0.51  # Condensation attempts                : 0
% 0.20/0.51  # Condensation successes               : 0
% 0.20/0.51  # Termbank termtop insertions          : 164297
% 0.20/0.51  
% 0.20/0.51  # -------------------------------------------------
% 0.20/0.51  # User time                : 0.156 s
% 0.20/0.51  # System time              : 0.012 s
% 0.20/0.51  # Total time               : 0.167 s
% 0.20/0.51  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
