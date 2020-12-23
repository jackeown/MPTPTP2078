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
% DateTime   : Thu Dec  3 10:58:45 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 149 expanded)
%              Number of clauses        :   28 (  63 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  164 ( 823 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   15 (   3 average)
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

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t202_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ! [X3] :
          ( r2_hidden(X3,k2_relat_1(X2))
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,negated_conjecture,(
    ! [X35] :
      ( ~ v1_xboole_0(esk2_0)
      & ~ v1_xboole_0(esk3_0)
      & ~ v1_xboole_0(esk4_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0)))
      & m1_subset_1(esk6_0,esk2_0)
      & ( ~ r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))
        | ~ m1_subset_1(X35,esk4_0)
        | ~ r2_hidden(k4_tarski(esk6_0,X35),esk5_0)
        | ~ r2_hidden(X35,esk3_0) )
      & ( m1_subset_1(esk7_0,esk4_0)
        | r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0)) )
      & ( r2_hidden(k4_tarski(esk6_0,esk7_0),esk5_0)
        | r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0)) )
      & ( r2_hidden(esk7_0,esk3_0)
        | r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).

fof(c_0_10,plain,(
    ! [X9,X10,X11,X13] :
      ( ( r2_hidden(esk1_3(X9,X10,X11),k2_relat_1(X11))
        | ~ r2_hidden(X9,k10_relat_1(X11,X10))
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(X9,esk1_3(X9,X10,X11)),X11)
        | ~ r2_hidden(X9,k10_relat_1(X11,X10))
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk1_3(X9,X10,X11),X10)
        | ~ r2_hidden(X9,k10_relat_1(X11,X10))
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(X13,k2_relat_1(X11))
        | ~ r2_hidden(k4_tarski(X9,X13),X11)
        | ~ r2_hidden(X13,X10)
        | r2_hidden(X9,k10_relat_1(X11,X10))
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_11,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))
    | ~ m1_subset_1(X1,esk4_0)
    | ~ r2_hidden(k4_tarski(esk6_0,X1),esk5_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,esk1_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X7,X8] :
      ( ~ r2_hidden(X7,X8)
      | m1_subset_1(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_14,negated_conjecture,
    ( ~ v1_relat_1(esk5_0)
    | ~ m1_subset_1(esk1_3(esk6_0,X1,esk5_0),esk4_0)
    | ~ r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))
    | ~ r2_hidden(esk1_3(esk6_0,X1,esk5_0),esk3_0)
    | ~ r2_hidden(esk6_0,k10_relat_1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | v1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_17,plain,(
    ! [X14,X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v5_relat_1(X15,X14)
      | ~ r2_hidden(X16,k2_relat_1(X15))
      | r2_hidden(X16,X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t202_relat_1])])])).

fof(c_0_18,plain,(
    ! [X23,X24,X25] :
      ( ( v4_relat_1(X25,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( v5_relat_1(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_relat_1(esk5_0)
    | ~ r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))
    | ~ r2_hidden(esk1_3(esk6_0,X1,esk5_0),esk3_0)
    | ~ r2_hidden(esk1_3(esk6_0,X1,esk5_0),esk4_0)
    | ~ r2_hidden(esk6_0,k10_relat_1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,plain,
    ( r2_hidden(X3,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ r2_hidden(X3,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X17,X18,X19] :
      ( ( r2_hidden(X17,k1_relat_1(X19))
        | ~ r2_hidden(k4_tarski(X17,X18),X19)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(X18,k2_relat_1(X19))
        | ~ r2_hidden(k4_tarski(X17,X18),X19)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_relat_1(esk5_0)
    | ~ r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))
    | ~ r2_hidden(esk1_3(esk6_0,esk3_0,esk5_0),esk4_0)
    | ~ r2_hidden(esk6_0,k10_relat_1(esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X4)
    | ~ v5_relat_1(X3,X4)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( v5_relat_1(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_22])).

cnf(c_0_31,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))
    | ~ r2_hidden(esk1_3(esk6_0,esk3_0,esk5_0),esk4_0)
    | ~ r2_hidden(esk6_0,k10_relat_1(esk5_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,esk5_0),esk4_0)
    | ~ r2_hidden(X1,k10_relat_1(esk5_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_28])])).

fof(c_0_35,plain,(
    ! [X26,X27,X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k8_relset_1(X26,X27,X28,X29) = k10_relat_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),esk5_0)
    | r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))
    | ~ r2_hidden(esk6_0,k10_relat_1(esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))
    | r2_hidden(esk6_0,k10_relat_1(esk5_0,X1))
    | ~ r2_hidden(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_28])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk7_0,esk3_0)
    | r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k10_relat_1(esk5_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_22])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_39]),c_0_22])]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.13/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t53_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k8_relset_1(X1,X3,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X5,X6),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relset_1)).
% 0.13/0.37  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 0.13/0.37  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.13/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.37  fof(t202_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>![X3]:(r2_hidden(X3,k2_relat_1(X2))=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 0.13/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.13/0.37  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 0.13/0.37  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.13/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k8_relset_1(X1,X3,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X5,X6),X4))&r2_hidden(X6,X2))))))))), inference(assume_negation,[status(cth)],[t53_relset_1])).
% 0.13/0.37  fof(c_0_9, negated_conjecture, ![X35]:(~v1_xboole_0(esk2_0)&(~v1_xboole_0(esk3_0)&(~v1_xboole_0(esk4_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0)))&(m1_subset_1(esk6_0,esk2_0)&((~r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))|(~m1_subset_1(X35,esk4_0)|~r2_hidden(k4_tarski(esk6_0,X35),esk5_0)|~r2_hidden(X35,esk3_0)))&(((m1_subset_1(esk7_0,esk4_0)|r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0)))&(r2_hidden(k4_tarski(esk6_0,esk7_0),esk5_0)|r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))))&(r2_hidden(esk7_0,esk3_0)|r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0)))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).
% 0.13/0.37  fof(c_0_10, plain, ![X9, X10, X11, X13]:((((r2_hidden(esk1_3(X9,X10,X11),k2_relat_1(X11))|~r2_hidden(X9,k10_relat_1(X11,X10))|~v1_relat_1(X11))&(r2_hidden(k4_tarski(X9,esk1_3(X9,X10,X11)),X11)|~r2_hidden(X9,k10_relat_1(X11,X10))|~v1_relat_1(X11)))&(r2_hidden(esk1_3(X9,X10,X11),X10)|~r2_hidden(X9,k10_relat_1(X11,X10))|~v1_relat_1(X11)))&(~r2_hidden(X13,k2_relat_1(X11))|~r2_hidden(k4_tarski(X9,X13),X11)|~r2_hidden(X13,X10)|r2_hidden(X9,k10_relat_1(X11,X10))|~v1_relat_1(X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (~r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))|~m1_subset_1(X1,esk4_0)|~r2_hidden(k4_tarski(esk6_0,X1),esk5_0)|~r2_hidden(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X1,esk1_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  fof(c_0_13, plain, ![X7, X8]:(~r2_hidden(X7,X8)|m1_subset_1(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (~v1_relat_1(esk5_0)|~m1_subset_1(esk1_3(esk6_0,X1,esk5_0),esk4_0)|~r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))|~r2_hidden(esk1_3(esk6_0,X1,esk5_0),esk3_0)|~r2_hidden(esk6_0,k10_relat_1(esk5_0,X1))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.37  cnf(c_0_15, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  fof(c_0_16, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|v1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.37  fof(c_0_17, plain, ![X14, X15, X16]:(~v1_relat_1(X15)|~v5_relat_1(X15,X14)|(~r2_hidden(X16,k2_relat_1(X15))|r2_hidden(X16,X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t202_relat_1])])])).
% 0.13/0.37  fof(c_0_18, plain, ![X23, X24, X25]:((v4_relat_1(X25,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(v5_relat_1(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (~v1_relat_1(esk5_0)|~r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))|~r2_hidden(esk1_3(esk6_0,X1,esk5_0),esk3_0)|~r2_hidden(esk1_3(esk6_0,X1,esk5_0),esk4_0)|~r2_hidden(esk6_0,k10_relat_1(esk5_0,X1))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.37  cnf(c_0_20, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_21, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_23, plain, (r2_hidden(X3,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~r2_hidden(X3,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_24, plain, (r2_hidden(esk1_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_25, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  fof(c_0_26, plain, ![X17, X18, X19]:((r2_hidden(X17,k1_relat_1(X19))|~r2_hidden(k4_tarski(X17,X18),X19)|~v1_relat_1(X19))&(r2_hidden(X18,k2_relat_1(X19))|~r2_hidden(k4_tarski(X17,X18),X19)|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (~v1_relat_1(esk5_0)|~r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))|~r2_hidden(esk1_3(esk6_0,esk3_0,esk5_0),esk4_0)|~r2_hidden(esk6_0,k10_relat_1(esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.37  cnf(c_0_29, plain, (r2_hidden(esk1_3(X1,X2,X3),X4)|~v5_relat_1(X3,X4)|~v1_relat_1(X3)|~r2_hidden(X1,k10_relat_1(X3,X2))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (v5_relat_1(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_22])).
% 0.13/0.37  cnf(c_0_31, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_32, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (~r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))|~r2_hidden(esk1_3(esk6_0,esk3_0,esk5_0),esk4_0)|~r2_hidden(esk6_0,k10_relat_1(esk5_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28])])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_3(X1,X2,esk5_0),esk4_0)|~r2_hidden(X1,k10_relat_1(esk5_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_28])])).
% 0.13/0.37  fof(c_0_35, plain, ![X26, X27, X28, X29]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k8_relset_1(X26,X27,X28,X29)=k10_relat_1(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.13/0.37  cnf(c_0_36, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk7_0),esk5_0)|r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (~r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))|~r2_hidden(esk6_0,k10_relat_1(esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.37  cnf(c_0_39, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))|r2_hidden(esk6_0,k10_relat_1(esk5_0,X1))|~r2_hidden(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_28])])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (r2_hidden(esk7_0,esk3_0)|r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (~r2_hidden(esk6_0,k10_relat_1(esk5_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_22])])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, (r2_hidden(esk6_0,k8_relset_1(esk2_0,esk4_0,esk5_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.13/0.37  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_39]), c_0_22])]), c_0_42]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 45
% 0.13/0.37  # Proof object clause steps            : 28
% 0.13/0.37  # Proof object formula steps           : 17
% 0.13/0.37  # Proof object conjectures             : 19
% 0.13/0.37  # Proof object clause conjectures      : 16
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 14
% 0.13/0.37  # Proof object initial formulas used   : 8
% 0.13/0.37  # Proof object generating inferences   : 12
% 0.13/0.37  # Proof object simplifying inferences  : 13
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 8
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 21
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 21
% 0.13/0.37  # Processed clauses                    : 71
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 2
% 0.13/0.37  # ...remaining for further processing  : 69
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 1
% 0.13/0.37  # Backward-rewritten                   : 17
% 0.13/0.37  # Generated clauses                    : 43
% 0.13/0.37  # ...of the previous two non-trivial   : 47
% 0.13/0.37  # Contextual simplify-reflections      : 1
% 0.13/0.37  # Paramodulations                      : 43
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 30
% 0.13/0.37  #    Positive orientable unit clauses  : 8
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 4
% 0.13/0.37  #    Non-unit-clauses                  : 18
% 0.13/0.37  # Current number of unprocessed clauses: 14
% 0.13/0.37  # ...number of literals in the above   : 47
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 39
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 237
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 100
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.37  # Unit Clause-clause subsumption calls : 27
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 4
% 0.13/0.37  # BW rewrite match successes           : 4
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2598
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
