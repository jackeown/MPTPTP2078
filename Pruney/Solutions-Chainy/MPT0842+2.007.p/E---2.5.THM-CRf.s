%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:45 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 149 expanded)
%              Number of clauses        :   30 (  65 expanded)
%              Number of leaves         :    7 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  178 ( 888 expanded)
%              Number of equality atoms :   24 (  71 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,k8_relset_1(X1,X3,X4,X2))
                      <=> ? [X6] :
                            ( m1_subset_1(X6,X3)
                            & r2_hidden(k4_tarski(X5,X6),X4)
                            & r2_hidden(X6,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ~ v1_xboole_0(X3)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( r2_hidden(X5,k8_relset_1(X1,X3,X4,X2))
                        <=> ? [X6] :
                              ( m1_subset_1(X6,X3)
                              & r2_hidden(k4_tarski(X5,X6),X4)
                              & r2_hidden(X6,X2) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t53_relset_1])).

fof(c_0_8,negated_conjecture,(
    ! [X40] :
      ( ~ v1_xboole_0(esk4_0)
      & ~ v1_xboole_0(esk5_0)
      & ~ v1_xboole_0(esk6_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0)))
      & m1_subset_1(esk8_0,esk4_0)
      & ( ~ r2_hidden(esk8_0,k8_relset_1(esk4_0,esk6_0,esk7_0,esk5_0))
        | ~ m1_subset_1(X40,esk6_0)
        | ~ r2_hidden(k4_tarski(esk8_0,X40),esk7_0)
        | ~ r2_hidden(X40,esk5_0) )
      & ( m1_subset_1(esk9_0,esk6_0)
        | r2_hidden(esk8_0,k8_relset_1(esk4_0,esk6_0,esk7_0,esk5_0)) )
      & ( r2_hidden(k4_tarski(esk8_0,esk9_0),esk7_0)
        | r2_hidden(esk8_0,k8_relset_1(esk4_0,esk6_0,esk7_0,esk5_0)) )
      & ( r2_hidden(esk9_0,esk5_0)
        | r2_hidden(esk8_0,k8_relset_1(esk4_0,esk6_0,esk7_0,esk5_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).

fof(c_0_9,plain,(
    ! [X16,X17,X18,X19,X21,X22,X23,X24,X26] :
      ( ( r2_hidden(k4_tarski(X19,esk1_4(X16,X17,X18,X19)),X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k10_relat_1(X16,X17)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk1_4(X16,X17,X18,X19),X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k10_relat_1(X16,X17)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X21,X22),X16)
        | ~ r2_hidden(X22,X17)
        | r2_hidden(X21,X18)
        | X18 != k10_relat_1(X16,X17)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(esk2_3(X16,X23,X24),X24)
        | ~ r2_hidden(k4_tarski(esk2_3(X16,X23,X24),X26),X16)
        | ~ r2_hidden(X26,X23)
        | X24 = k10_relat_1(X16,X23)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk2_3(X16,X23,X24),esk3_3(X16,X23,X24)),X16)
        | r2_hidden(esk2_3(X16,X23,X24),X24)
        | X24 = k10_relat_1(X16,X23)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk3_3(X16,X23,X24),X23)
        | r2_hidden(esk2_3(X16,X23,X24),X24)
        | X24 = k10_relat_1(X16,X23)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_10,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | v1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_11,plain,(
    ! [X31,X32,X33,X34] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k8_relset_1(X31,X32,X33,X34) = k10_relat_1(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_12,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k8_relset_1(esk4_0,esk6_0,esk7_0,esk5_0))
    | ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(esk8_0,X1),esk7_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,X4,X1)),X2)
    | ~ r2_hidden(X1,X4)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( X1 != k10_relat_1(esk7_0,X2)
    | ~ v1_relat_1(esk7_0)
    | ~ m1_subset_1(esk1_4(esk7_0,X2,X1,esk8_0),esk6_0)
    | ~ r2_hidden(esk8_0,k8_relset_1(esk4_0,esk6_0,esk7_0,esk5_0))
    | ~ r2_hidden(esk1_4(esk7_0,X2,X1,esk8_0),esk5_0)
    | ~ r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk9_0),esk7_0)
    | r2_hidden(esk8_0,k8_relset_1(esk4_0,esk6_0,esk7_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( k8_relset_1(esk4_0,esk6_0,esk7_0,X1) = k10_relat_1(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( X1 != k10_relat_1(esk7_0,X2)
    | ~ m1_subset_1(esk1_4(esk7_0,X2,X1,esk8_0),esk6_0)
    | ~ r2_hidden(esk8_0,k8_relset_1(esk4_0,esk6_0,esk7_0,esk5_0))
    | ~ r2_hidden(esk1_4(esk7_0,X2,X1,esk8_0),esk5_0)
    | ~ r2_hidden(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18])])).

fof(c_0_22,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(X14,X15)
      | m1_subset_1(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk9_0),esk7_0)
    | r2_hidden(esk8_0,k10_relat_1(esk7_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_25,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | ~ r2_hidden(X13,X12)
      | r2_hidden(X13,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_26,negated_conjecture,
    ( X1 != k10_relat_1(esk7_0,X2)
    | ~ m1_subset_1(esk1_4(esk7_0,X2,X1,esk8_0),esk6_0)
    | ~ r2_hidden(esk1_4(esk7_0,X2,X1,esk8_0),esk5_0)
    | ~ r2_hidden(esk8_0,k10_relat_1(esk7_0,esk5_0))
    | ~ r2_hidden(esk8_0,X1) ),
    inference(rw,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk8_0,k10_relat_1(esk7_0,esk5_0))
    | r2_hidden(esk8_0,X1)
    | X1 != k10_relat_1(esk7_0,X2)
    | ~ r2_hidden(esk9_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_18])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk9_0,esk5_0)
    | r2_hidden(esk8_0,k8_relset_1(esk4_0,esk6_0,esk7_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( X1 != k10_relat_1(esk7_0,X2)
    | ~ r2_hidden(esk1_4(esk7_0,X2,X1,esk8_0),esk5_0)
    | ~ r2_hidden(esk1_4(esk7_0,X2,X1,esk8_0),esk6_0)
    | ~ r2_hidden(esk8_0,k10_relat_1(esk7_0,esk5_0))
    | ~ r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk8_0,k10_relat_1(esk7_0,esk5_0))
    | r2_hidden(esk8_0,k10_relat_1(esk7_0,X1))
    | ~ r2_hidden(esk9_0,X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk8_0,k10_relat_1(esk7_0,esk5_0))
    | r2_hidden(esk9_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_20])).

fof(c_0_35,plain,(
    ! [X7,X8,X9,X10] :
      ( ( r2_hidden(X7,X9)
        | ~ r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)) )
      & ( r2_hidden(X8,X10)
        | ~ r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)) )
      & ( ~ r2_hidden(X7,X9)
        | ~ r2_hidden(X8,X10)
        | r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk4_0,esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( X1 != k10_relat_1(esk7_0,esk5_0)
    | ~ r2_hidden(esk1_4(esk7_0,esk5_0,X1,esk8_0),esk6_0)
    | ~ r2_hidden(esk8_0,k10_relat_1(esk7_0,esk5_0))
    | ~ r2_hidden(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_18])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk8_0,k10_relat_1(esk7_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk1_4(esk7_0,X2,X3,X1)),k2_zfmisc_1(esk4_0,esk6_0))
    | X3 != k10_relat_1(esk7_0,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_13]),c_0_18])])).

cnf(c_0_41,negated_conjecture,
    ( X1 != k10_relat_1(esk7_0,esk5_0)
    | ~ r2_hidden(esk1_4(esk7_0,esk5_0,X1,esk8_0),esk6_0)
    | ~ r2_hidden(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_4(esk7_0,X1,X2,X3),esk6_0)
    | X2 != k10_relat_1(esk7_0,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( X1 != k10_relat_1(esk7_0,esk5_0)
    | ~ r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_43,c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:39:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.19/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t53_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k8_relset_1(X1,X3,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X5,X6),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relset_1)).
% 0.19/0.38  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 0.19/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.38  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.19/0.38  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.19/0.38  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.38  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.19/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k8_relset_1(X1,X3,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X5,X6),X4))&r2_hidden(X6,X2))))))))), inference(assume_negation,[status(cth)],[t53_relset_1])).
% 0.19/0.38  fof(c_0_8, negated_conjecture, ![X40]:(~v1_xboole_0(esk4_0)&(~v1_xboole_0(esk5_0)&(~v1_xboole_0(esk6_0)&(m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0)))&(m1_subset_1(esk8_0,esk4_0)&((~r2_hidden(esk8_0,k8_relset_1(esk4_0,esk6_0,esk7_0,esk5_0))|(~m1_subset_1(X40,esk6_0)|~r2_hidden(k4_tarski(esk8_0,X40),esk7_0)|~r2_hidden(X40,esk5_0)))&(((m1_subset_1(esk9_0,esk6_0)|r2_hidden(esk8_0,k8_relset_1(esk4_0,esk6_0,esk7_0,esk5_0)))&(r2_hidden(k4_tarski(esk8_0,esk9_0),esk7_0)|r2_hidden(esk8_0,k8_relset_1(esk4_0,esk6_0,esk7_0,esk5_0))))&(r2_hidden(esk9_0,esk5_0)|r2_hidden(esk8_0,k8_relset_1(esk4_0,esk6_0,esk7_0,esk5_0)))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).
% 0.19/0.38  fof(c_0_9, plain, ![X16, X17, X18, X19, X21, X22, X23, X24, X26]:((((r2_hidden(k4_tarski(X19,esk1_4(X16,X17,X18,X19)),X16)|~r2_hidden(X19,X18)|X18!=k10_relat_1(X16,X17)|~v1_relat_1(X16))&(r2_hidden(esk1_4(X16,X17,X18,X19),X17)|~r2_hidden(X19,X18)|X18!=k10_relat_1(X16,X17)|~v1_relat_1(X16)))&(~r2_hidden(k4_tarski(X21,X22),X16)|~r2_hidden(X22,X17)|r2_hidden(X21,X18)|X18!=k10_relat_1(X16,X17)|~v1_relat_1(X16)))&((~r2_hidden(esk2_3(X16,X23,X24),X24)|(~r2_hidden(k4_tarski(esk2_3(X16,X23,X24),X26),X16)|~r2_hidden(X26,X23))|X24=k10_relat_1(X16,X23)|~v1_relat_1(X16))&((r2_hidden(k4_tarski(esk2_3(X16,X23,X24),esk3_3(X16,X23,X24)),X16)|r2_hidden(esk2_3(X16,X23,X24),X24)|X24=k10_relat_1(X16,X23)|~v1_relat_1(X16))&(r2_hidden(esk3_3(X16,X23,X24),X23)|r2_hidden(esk2_3(X16,X23,X24),X24)|X24=k10_relat_1(X16,X23)|~v1_relat_1(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.19/0.38  fof(c_0_10, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|v1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.38  fof(c_0_11, plain, ![X31, X32, X33, X34]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k8_relset_1(X31,X32,X33,X34)=k10_relat_1(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.19/0.38  cnf(c_0_12, negated_conjecture, (~r2_hidden(esk8_0,k8_relset_1(esk4_0,esk6_0,esk7_0,esk5_0))|~m1_subset_1(X1,esk6_0)|~r2_hidden(k4_tarski(esk8_0,X1),esk7_0)|~r2_hidden(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_13, plain, (r2_hidden(k4_tarski(X1,esk1_4(X2,X3,X4,X1)),X2)|~r2_hidden(X1,X4)|X4!=k10_relat_1(X2,X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_14, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_16, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (X1!=k10_relat_1(esk7_0,X2)|~v1_relat_1(esk7_0)|~m1_subset_1(esk1_4(esk7_0,X2,X1,esk8_0),esk6_0)|~r2_hidden(esk8_0,k8_relset_1(esk4_0,esk6_0,esk7_0,esk5_0))|~r2_hidden(esk1_4(esk7_0,X2,X1,esk8_0),esk5_0)|~r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk9_0),esk7_0)|r2_hidden(esk8_0,k8_relset_1(esk4_0,esk6_0,esk7_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (k8_relset_1(esk4_0,esk6_0,esk7_0,X1)=k10_relat_1(esk7_0,X1)), inference(spm,[status(thm)],[c_0_16, c_0_15])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (X1!=k10_relat_1(esk7_0,X2)|~m1_subset_1(esk1_4(esk7_0,X2,X1,esk8_0),esk6_0)|~r2_hidden(esk8_0,k8_relset_1(esk4_0,esk6_0,esk7_0,esk5_0))|~r2_hidden(esk1_4(esk7_0,X2,X1,esk8_0),esk5_0)|~r2_hidden(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18])])).
% 0.19/0.38  fof(c_0_22, plain, ![X14, X15]:(~r2_hidden(X14,X15)|m1_subset_1(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.19/0.38  cnf(c_0_23, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk9_0),esk7_0)|r2_hidden(esk8_0,k10_relat_1(esk7_0,esk5_0))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.38  fof(c_0_25, plain, ![X11, X12, X13]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|(~r2_hidden(X13,X12)|r2_hidden(X13,X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (X1!=k10_relat_1(esk7_0,X2)|~m1_subset_1(esk1_4(esk7_0,X2,X1,esk8_0),esk6_0)|~r2_hidden(esk1_4(esk7_0,X2,X1,esk8_0),esk5_0)|~r2_hidden(esk8_0,k10_relat_1(esk7_0,esk5_0))|~r2_hidden(esk8_0,X1)), inference(rw,[status(thm)],[c_0_21, c_0_20])).
% 0.19/0.38  cnf(c_0_27, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk8_0,k10_relat_1(esk7_0,esk5_0))|r2_hidden(esk8_0,X1)|X1!=k10_relat_1(esk7_0,X2)|~r2_hidden(esk9_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_18])])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(esk9_0,esk5_0)|r2_hidden(esk8_0,k8_relset_1(esk4_0,esk6_0,esk7_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_30, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (X1!=k10_relat_1(esk7_0,X2)|~r2_hidden(esk1_4(esk7_0,X2,X1,esk8_0),esk5_0)|~r2_hidden(esk1_4(esk7_0,X2,X1,esk8_0),esk6_0)|~r2_hidden(esk8_0,k10_relat_1(esk7_0,esk5_0))|~r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.38  cnf(c_0_32, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (r2_hidden(esk8_0,k10_relat_1(esk7_0,esk5_0))|r2_hidden(esk8_0,k10_relat_1(esk7_0,X1))|~r2_hidden(esk9_0,X1)), inference(er,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(esk8_0,k10_relat_1(esk7_0,esk5_0))|r2_hidden(esk9_0,esk5_0)), inference(rw,[status(thm)],[c_0_29, c_0_20])).
% 0.19/0.38  fof(c_0_35, plain, ![X7, X8, X9, X10]:(((r2_hidden(X7,X9)|~r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)))&(r2_hidden(X8,X10)|~r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10))))&(~r2_hidden(X7,X9)|~r2_hidden(X8,X10)|r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk4_0,esk6_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_30, c_0_15])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (X1!=k10_relat_1(esk7_0,esk5_0)|~r2_hidden(esk1_4(esk7_0,esk5_0,X1,esk8_0),esk6_0)|~r2_hidden(esk8_0,k10_relat_1(esk7_0,esk5_0))|~r2_hidden(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_18])])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk8_0,k10_relat_1(esk7_0,esk5_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.38  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(X1,esk1_4(esk7_0,X2,X3,X1)),k2_zfmisc_1(esk4_0,esk6_0))|X3!=k10_relat_1(esk7_0,X2)|~r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_13]), c_0_18])])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (X1!=k10_relat_1(esk7_0,esk5_0)|~r2_hidden(esk1_4(esk7_0,esk5_0,X1,esk8_0),esk6_0)|~r2_hidden(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38])])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (r2_hidden(esk1_4(esk7_0,X1,X2,X3),esk6_0)|X2!=k10_relat_1(esk7_0,X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (X1!=k10_relat_1(esk7_0,esk5_0)|~r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_43, c_0_38]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 45
% 0.19/0.38  # Proof object clause steps            : 30
% 0.19/0.38  # Proof object formula steps           : 15
% 0.19/0.38  # Proof object conjectures             : 25
% 0.19/0.38  # Proof object clause conjectures      : 22
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 12
% 0.19/0.38  # Proof object initial formulas used   : 7
% 0.19/0.38  # Proof object generating inferences   : 13
% 0.19/0.38  # Proof object simplifying inferences  : 13
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 7
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 22
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 22
% 0.19/0.38  # Processed clauses                    : 88
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 6
% 0.19/0.38  # ...remaining for further processing  : 82
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 2
% 0.19/0.38  # Backward-rewritten                   : 19
% 0.19/0.38  # Generated clauses                    : 81
% 0.19/0.38  # ...of the previous two non-trivial   : 87
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 77
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 4
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 39
% 0.19/0.38  #    Positive orientable unit clauses  : 6
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 3
% 0.19/0.38  #    Non-unit-clauses                  : 30
% 0.19/0.38  # Current number of unprocessed clauses: 35
% 0.19/0.38  # ...number of literals in the above   : 171
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 43
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 902
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 296
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 7
% 0.19/0.38  # Unit Clause-clause subsumption calls : 4
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 3
% 0.19/0.38  # BW rewrite match successes           : 3
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 3547
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.030 s
% 0.19/0.38  # System time              : 0.007 s
% 0.19/0.38  # Total time               : 0.038 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
