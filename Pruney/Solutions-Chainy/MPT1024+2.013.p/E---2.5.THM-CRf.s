%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:28 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   43 (  96 expanded)
%              Number of clauses        :   26 (  39 expanded)
%              Number of leaves         :    8 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  175 ( 515 expanded)
%              Number of equality atoms :   36 (  94 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   44 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t115_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ~ ( r2_hidden(X6,X1)
                  & r2_hidden(X6,X3)
                  & X5 = k1_funct_1(X4,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

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

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
              & ! [X6] :
                  ~ ( r2_hidden(X6,X1)
                    & r2_hidden(X6,X3)
                    & X5 = k1_funct_1(X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t115_funct_2])).

fof(c_0_9,plain,(
    ! [X29,X30,X31] :
      ( ( v4_relat_1(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( v5_relat_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_10,negated_conjecture,(
    ! [X41] :
      ( v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,esk4_0,esk5_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))
      & ( ~ r2_hidden(X41,esk4_0)
        | ~ r2_hidden(X41,esk6_0)
        | esk8_0 != k1_funct_1(esk7_0,X41) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | v1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_12,plain,(
    ! [X14,X15,X16,X17,X19,X20,X21,X22,X24] :
      ( ( r2_hidden(esk1_4(X14,X15,X16,X17),k1_relat_1(X14))
        | ~ r2_hidden(X17,X16)
        | X16 != k9_relat_1(X14,X15)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( r2_hidden(esk1_4(X14,X15,X16,X17),X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k9_relat_1(X14,X15)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( X17 = k1_funct_1(X14,esk1_4(X14,X15,X16,X17))
        | ~ r2_hidden(X17,X16)
        | X16 != k9_relat_1(X14,X15)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( ~ r2_hidden(X20,k1_relat_1(X14))
        | ~ r2_hidden(X20,X15)
        | X19 != k1_funct_1(X14,X20)
        | r2_hidden(X19,X16)
        | X16 != k9_relat_1(X14,X15)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( ~ r2_hidden(esk2_3(X14,X21,X22),X22)
        | ~ r2_hidden(X24,k1_relat_1(X14))
        | ~ r2_hidden(X24,X21)
        | esk2_3(X14,X21,X22) != k1_funct_1(X14,X24)
        | X22 = k9_relat_1(X14,X21)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( r2_hidden(esk3_3(X14,X21,X22),k1_relat_1(X14))
        | r2_hidden(esk2_3(X14,X21,X22),X22)
        | X22 = k9_relat_1(X14,X21)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( r2_hidden(esk3_3(X14,X21,X22),X21)
        | r2_hidden(esk2_3(X14,X21,X22),X22)
        | X22 = k9_relat_1(X14,X21)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( esk2_3(X14,X21,X22) = k1_funct_1(X14,esk3_3(X14,X21,X22))
        | r2_hidden(esk2_3(X14,X21,X22),X22)
        | X22 = k9_relat_1(X14,X21)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_13,plain,(
    ! [X12,X13] :
      ( ( ~ v4_relat_1(X13,X12)
        | r1_tarski(k1_relat_1(X13),X12)
        | ~ v1_relat_1(X13) )
      & ( ~ r1_tarski(k1_relat_1(X13),X12)
        | v4_relat_1(X13,X12)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_14,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk6_0)
    | esk8_0 != k1_funct_1(esk7_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( X1 = k1_funct_1(X2,esk1_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_20,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X10,k1_zfmisc_1(X11))
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | m1_subset_1(X10,k1_zfmisc_1(X11)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( v4_relat_1(esk7_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( X1 != k9_relat_1(esk7_0,X2)
    | esk8_0 != X3
    | ~ v1_relat_1(esk7_0)
    | ~ r2_hidden(esk1_4(esk7_0,X2,X1,X3),esk4_0)
    | ~ r2_hidden(esk1_4(esk7_0,X2,X1,X3),esk6_0)
    | ~ r2_hidden(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

fof(c_0_25,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | ~ r2_hidden(X9,X8)
      | r2_hidden(X9,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk7_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_28,negated_conjecture,
    ( X1 != k9_relat_1(esk7_0,X2)
    | esk8_0 != X3
    | ~ r2_hidden(esk1_4(esk7_0,X2,X1,X3),esk4_0)
    | ~ r2_hidden(esk1_4(esk7_0,X2,X1,X3),esk6_0)
    | ~ r2_hidden(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_23])])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk7_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( X1 != k9_relat_1(esk7_0,esk6_0)
    | esk8_0 != X2
    | ~ r2_hidden(esk1_4(esk7_0,esk6_0,X1,X2),esk4_0)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_19]),c_0_23])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( X1 != k9_relat_1(esk7_0,esk6_0)
    | esk8_0 != X2
    | ~ r2_hidden(esk1_4(esk7_0,esk6_0,X1,X2),k1_relat_1(esk7_0))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_36,plain,(
    ! [X32,X33,X34,X35] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k7_relset_1(X32,X33,X34,X35) = k9_relat_1(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_37,negated_conjecture,
    ( X1 != k9_relat_1(esk7_0,esk6_0)
    | esk8_0 != X2
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_19]),c_0_23])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( esk8_0 != X1
    | ~ r2_hidden(X1,k9_relat_1(esk7_0,esk6_0)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk8_0,k9_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_15])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_40,c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:35:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t115_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 0.14/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.14/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.14/0.38  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 0.14/0.38  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.14/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.14/0.38  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.14/0.38  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.14/0.38  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6))))))), inference(assume_negation,[status(cth)],[t115_funct_2])).
% 0.14/0.38  fof(c_0_9, plain, ![X29, X30, X31]:((v4_relat_1(X31,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(v5_relat_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.14/0.38  fof(c_0_10, negated_conjecture, ![X41]:(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk4_0,esk5_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))&(~r2_hidden(X41,esk4_0)|~r2_hidden(X41,esk6_0)|esk8_0!=k1_funct_1(esk7_0,X41)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.14/0.38  fof(c_0_11, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|v1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.14/0.38  fof(c_0_12, plain, ![X14, X15, X16, X17, X19, X20, X21, X22, X24]:(((((r2_hidden(esk1_4(X14,X15,X16,X17),k1_relat_1(X14))|~r2_hidden(X17,X16)|X16!=k9_relat_1(X14,X15)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(r2_hidden(esk1_4(X14,X15,X16,X17),X15)|~r2_hidden(X17,X16)|X16!=k9_relat_1(X14,X15)|(~v1_relat_1(X14)|~v1_funct_1(X14))))&(X17=k1_funct_1(X14,esk1_4(X14,X15,X16,X17))|~r2_hidden(X17,X16)|X16!=k9_relat_1(X14,X15)|(~v1_relat_1(X14)|~v1_funct_1(X14))))&(~r2_hidden(X20,k1_relat_1(X14))|~r2_hidden(X20,X15)|X19!=k1_funct_1(X14,X20)|r2_hidden(X19,X16)|X16!=k9_relat_1(X14,X15)|(~v1_relat_1(X14)|~v1_funct_1(X14))))&((~r2_hidden(esk2_3(X14,X21,X22),X22)|(~r2_hidden(X24,k1_relat_1(X14))|~r2_hidden(X24,X21)|esk2_3(X14,X21,X22)!=k1_funct_1(X14,X24))|X22=k9_relat_1(X14,X21)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(((r2_hidden(esk3_3(X14,X21,X22),k1_relat_1(X14))|r2_hidden(esk2_3(X14,X21,X22),X22)|X22=k9_relat_1(X14,X21)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(r2_hidden(esk3_3(X14,X21,X22),X21)|r2_hidden(esk2_3(X14,X21,X22),X22)|X22=k9_relat_1(X14,X21)|(~v1_relat_1(X14)|~v1_funct_1(X14))))&(esk2_3(X14,X21,X22)=k1_funct_1(X14,esk3_3(X14,X21,X22))|r2_hidden(esk2_3(X14,X21,X22),X22)|X22=k9_relat_1(X14,X21)|(~v1_relat_1(X14)|~v1_funct_1(X14)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 0.14/0.38  fof(c_0_13, plain, ![X12, X13]:((~v4_relat_1(X13,X12)|r1_tarski(k1_relat_1(X13),X12)|~v1_relat_1(X13))&(~r1_tarski(k1_relat_1(X13),X12)|v4_relat_1(X13,X12)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.14/0.38  cnf(c_0_14, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_16, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk6_0)|esk8_0!=k1_funct_1(esk7_0,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_18, plain, (X1=k1_funct_1(X2,esk1_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  fof(c_0_20, plain, ![X10, X11]:((~m1_subset_1(X10,k1_zfmisc_1(X11))|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|m1_subset_1(X10,k1_zfmisc_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.14/0.38  cnf(c_0_21, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (v4_relat_1(esk7_0,esk4_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_16, c_0_15])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (X1!=k9_relat_1(esk7_0,X2)|esk8_0!=X3|~v1_relat_1(esk7_0)|~r2_hidden(esk1_4(esk7_0,X2,X1,X3),esk4_0)|~r2_hidden(esk1_4(esk7_0,X2,X1,X3),esk6_0)|~r2_hidden(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.14/0.38  fof(c_0_25, plain, ![X7, X8, X9]:(~m1_subset_1(X8,k1_zfmisc_1(X7))|(~r2_hidden(X9,X8)|r2_hidden(X9,X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.14/0.38  cnf(c_0_26, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (r1_tarski(k1_relat_1(esk7_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (X1!=k9_relat_1(esk7_0,X2)|esk8_0!=X3|~r2_hidden(esk1_4(esk7_0,X2,X1,X3),esk4_0)|~r2_hidden(esk1_4(esk7_0,X2,X1,X3),esk6_0)|~r2_hidden(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_23])])).
% 0.14/0.38  cnf(c_0_29, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_30, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (m1_subset_1(k1_relat_1(esk7_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (X1!=k9_relat_1(esk7_0,esk6_0)|esk8_0!=X2|~r2_hidden(esk1_4(esk7_0,esk6_0,X1,X2),esk4_0)|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_19]), c_0_23])])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (X1!=k9_relat_1(esk7_0,esk6_0)|esk8_0!=X2|~r2_hidden(esk1_4(esk7_0,esk6_0,X1,X2),k1_relat_1(esk7_0))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.14/0.38  cnf(c_0_35, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),k1_relat_1(X1))|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  fof(c_0_36, plain, ![X32, X33, X34, X35]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k7_relset_1(X32,X33,X34,X35)=k9_relat_1(X34,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (X1!=k9_relat_1(esk7_0,esk6_0)|esk8_0!=X2|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_19]), c_0_23])])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_39, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (esk8_0!=X1|~r2_hidden(X1,k9_relat_1(esk7_0,esk6_0))), inference(er,[status(thm)],[c_0_37])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (r2_hidden(esk8_0,k9_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_15])])).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_40, c_0_41]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 43
% 0.14/0.38  # Proof object clause steps            : 26
% 0.14/0.38  # Proof object formula steps           : 17
% 0.14/0.38  # Proof object conjectures             : 20
% 0.14/0.38  # Proof object clause conjectures      : 17
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 13
% 0.14/0.38  # Proof object initial formulas used   : 8
% 0.14/0.38  # Proof object generating inferences   : 12
% 0.14/0.38  # Proof object simplifying inferences  : 14
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 8
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 22
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 22
% 0.14/0.38  # Processed clauses                    : 60
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 60
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 2
% 0.14/0.38  # Backward-rewritten                   : 1
% 0.14/0.38  # Generated clauses                    : 25
% 0.14/0.38  # ...of the previous two non-trivial   : 21
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 23
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 2
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 35
% 0.14/0.38  #    Positive orientable unit clauses  : 10
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 0
% 0.14/0.38  #    Non-unit-clauses                  : 25
% 0.14/0.38  # Current number of unprocessed clauses: 4
% 0.14/0.38  # ...number of literals in the above   : 24
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 25
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 146
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 16
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.14/0.38  # Unit Clause-clause subsumption calls : 2
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 2514
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.032 s
% 0.14/0.38  # System time              : 0.002 s
% 0.14/0.38  # Total time               : 0.034 s
% 0.14/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
