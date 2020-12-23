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
% DateTime   : Thu Dec  3 10:58:48 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 236 expanded)
%              Number of clauses        :   40 (  97 expanded)
%              Number of leaves         :    9 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :  209 (1335 expanded)
%              Number of equality atoms :   15 (  52 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   15 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

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

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
    ! [X36,X37,X38,X39] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k8_relset_1(X36,X37,X38,X39) = k10_relat_1(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_11,negated_conjecture,(
    ! [X45] :
      ( ~ v1_xboole_0(esk5_0)
      & ~ v1_xboole_0(esk6_0)
      & ~ v1_xboole_0(esk7_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))
      & m1_subset_1(esk9_0,esk5_0)
      & ( ~ r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
        | ~ m1_subset_1(X45,esk7_0)
        | ~ r2_hidden(k4_tarski(esk9_0,X45),esk8_0)
        | ~ r2_hidden(X45,esk6_0) )
      & ( m1_subset_1(esk10_0,esk7_0)
        | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) )
      & ( r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)
        | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) )
      & ( r2_hidden(esk10_0,esk6_0)
        | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).

fof(c_0_12,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | ~ r2_hidden(X15,X14)
      | r2_hidden(X15,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_13,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | v1_relat_1(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_16,plain,(
    ! [X29,X30] : v1_relat_1(k2_zfmisc_1(X29,X30)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_17,plain,(
    ! [X18,X19,X20,X22,X23,X24,X25,X27] :
      ( ( ~ r2_hidden(X20,X19)
        | r2_hidden(k4_tarski(esk1_3(X18,X19,X20),X20),X18)
        | X19 != k2_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X23,X22),X18)
        | r2_hidden(X22,X19)
        | X19 != k2_relat_1(X18) )
      & ( ~ r2_hidden(esk2_2(X24,X25),X25)
        | ~ r2_hidden(k4_tarski(X27,esk2_2(X24,X25)),X24)
        | X25 = k2_relat_1(X24) )
      & ( r2_hidden(esk2_2(X24,X25),X25)
        | r2_hidden(k4_tarski(esk3_2(X24,X25),esk2_2(X24,X25)),X24)
        | X25 = k2_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_18,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X12,X11)
        | r2_hidden(X12,X11)
        | v1_xboole_0(X11) )
      & ( ~ r2_hidden(X12,X11)
        | m1_subset_1(X12,X11)
        | v1_xboole_0(X11) )
      & ( ~ m1_subset_1(X12,X11)
        | v1_xboole_0(X12)
        | ~ v1_xboole_0(X11) )
      & ( ~ v1_xboole_0(X12)
        | m1_subset_1(X12,X11)
        | ~ v1_xboole_0(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X31,X32,X33,X35] :
      ( ( r2_hidden(esk4_3(X31,X32,X33),k2_relat_1(X33))
        | ~ r2_hidden(X31,k10_relat_1(X33,X32))
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(k4_tarski(X31,esk4_3(X31,X32,X33)),X33)
        | ~ r2_hidden(X31,k10_relat_1(X33,X32))
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(esk4_3(X31,X32,X33),X32)
        | ~ r2_hidden(X31,k10_relat_1(X33,X32))
        | ~ v1_relat_1(X33) )
      & ( ~ r2_hidden(X35,k2_relat_1(X33))
        | ~ r2_hidden(k4_tarski(X31,X35),X33)
        | ~ r2_hidden(X35,X32)
        | r2_hidden(X31,k10_relat_1(X33,X32))
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)
    | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( k8_relset_1(esk5_0,esk7_0,esk8_0,X1) = k10_relat_1(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_23,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk10_0,esk6_0)
    | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_29,plain,(
    ! [X7,X8,X9,X10] :
      ( ( r2_hidden(X7,X9)
        | ~ r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)) )
      & ( r2_hidden(X8,X10)
        | ~ r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)) )
      & ( ~ r2_hidden(X7,X9)
        | ~ r2_hidden(X8,X10)
        | r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk5_0,esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_14])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)
    | r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_14]),c_0_24])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | r2_hidden(esk10_0,X1)
    | X1 != k2_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk10_0,esk6_0)
    | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_3(esk8_0,X1,X2),X2),k2_zfmisc_1(esk5_0,esk7_0))
    | X1 != k2_relat_1(esk8_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))
    | r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))
    | ~ r2_hidden(esk10_0,k2_relat_1(esk8_0))
    | ~ r2_hidden(esk10_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))
    | r2_hidden(esk10_0,X1)
    | X1 != k2_relat_1(esk8_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_22])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk10_0,esk6_0)
    | r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | X2 != k2_relat_1(esk8_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | ~ m1_subset_1(X1,esk7_0)
    | ~ r2_hidden(k4_tarski(esk9_0,X1),esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))
    | r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))
    | ~ r2_hidden(esk10_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))
    | r2_hidden(esk10_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_48,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( ~ m1_subset_1(X1,esk7_0)
    | ~ r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))
    | ~ r2_hidden(k4_tarski(esk9_0,X1),esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk4_3(X1,X2,esk8_0),esk7_0)
    | ~ r2_hidden(X1,k10_relat_1(esk8_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_34])])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_53,negated_conjecture,
    ( ~ m1_subset_1(X1,esk7_0)
    | ~ r2_hidden(k4_tarski(esk9_0,X1),esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])])).

cnf(c_0_54,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk4_3(X1,X2,esk8_0),esk7_0)
    | ~ r2_hidden(X1,k10_relat_1(esk8_0,X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_51]),c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)
    | ~ r2_hidden(esk9_0,k10_relat_1(esk8_0,X1)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_34])]),c_0_55])).

cnf(c_0_57,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_50]),c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n006.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 14:54:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.52  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.17/0.52  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.17/0.52  #
% 0.17/0.52  # Preprocessing time       : 0.029 s
% 0.17/0.52  # Presaturation interreduction done
% 0.17/0.52  
% 0.17/0.52  # Proof found!
% 0.17/0.52  # SZS status Theorem
% 0.17/0.52  # SZS output start CNFRefutation
% 0.17/0.52  fof(t53_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k8_relset_1(X1,X3,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X5,X6),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_relset_1)).
% 0.17/0.52  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.17/0.52  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.17/0.52  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.17/0.52  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.17/0.52  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.17/0.52  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.17/0.52  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.17/0.52  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.17/0.52  fof(c_0_9, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k8_relset_1(X1,X3,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X5,X6),X4))&r2_hidden(X6,X2))))))))), inference(assume_negation,[status(cth)],[t53_relset_1])).
% 0.17/0.52  fof(c_0_10, plain, ![X36, X37, X38, X39]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|k8_relset_1(X36,X37,X38,X39)=k10_relat_1(X38,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.17/0.52  fof(c_0_11, negated_conjecture, ![X45]:(~v1_xboole_0(esk5_0)&(~v1_xboole_0(esk6_0)&(~v1_xboole_0(esk7_0)&(m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))&(m1_subset_1(esk9_0,esk5_0)&((~r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|(~m1_subset_1(X45,esk7_0)|~r2_hidden(k4_tarski(esk9_0,X45),esk8_0)|~r2_hidden(X45,esk6_0)))&(((m1_subset_1(esk10_0,esk7_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)))&(r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))))&(r2_hidden(esk10_0,esk6_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).
% 0.17/0.52  fof(c_0_12, plain, ![X13, X14, X15]:(~m1_subset_1(X14,k1_zfmisc_1(X13))|(~r2_hidden(X15,X14)|r2_hidden(X15,X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.17/0.52  cnf(c_0_13, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.52  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.52  fof(c_0_15, plain, ![X16, X17]:(~v1_relat_1(X16)|(~m1_subset_1(X17,k1_zfmisc_1(X16))|v1_relat_1(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.17/0.52  fof(c_0_16, plain, ![X29, X30]:v1_relat_1(k2_zfmisc_1(X29,X30)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.17/0.52  fof(c_0_17, plain, ![X18, X19, X20, X22, X23, X24, X25, X27]:(((~r2_hidden(X20,X19)|r2_hidden(k4_tarski(esk1_3(X18,X19,X20),X20),X18)|X19!=k2_relat_1(X18))&(~r2_hidden(k4_tarski(X23,X22),X18)|r2_hidden(X22,X19)|X19!=k2_relat_1(X18)))&((~r2_hidden(esk2_2(X24,X25),X25)|~r2_hidden(k4_tarski(X27,esk2_2(X24,X25)),X24)|X25=k2_relat_1(X24))&(r2_hidden(esk2_2(X24,X25),X25)|r2_hidden(k4_tarski(esk3_2(X24,X25),esk2_2(X24,X25)),X24)|X25=k2_relat_1(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.17/0.52  fof(c_0_18, plain, ![X11, X12]:(((~m1_subset_1(X12,X11)|r2_hidden(X12,X11)|v1_xboole_0(X11))&(~r2_hidden(X12,X11)|m1_subset_1(X12,X11)|v1_xboole_0(X11)))&((~m1_subset_1(X12,X11)|v1_xboole_0(X12)|~v1_xboole_0(X11))&(~v1_xboole_0(X12)|m1_subset_1(X12,X11)|~v1_xboole_0(X11)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.17/0.52  cnf(c_0_19, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.17/0.52  fof(c_0_20, plain, ![X31, X32, X33, X35]:((((r2_hidden(esk4_3(X31,X32,X33),k2_relat_1(X33))|~r2_hidden(X31,k10_relat_1(X33,X32))|~v1_relat_1(X33))&(r2_hidden(k4_tarski(X31,esk4_3(X31,X32,X33)),X33)|~r2_hidden(X31,k10_relat_1(X33,X32))|~v1_relat_1(X33)))&(r2_hidden(esk4_3(X31,X32,X33),X32)|~r2_hidden(X31,k10_relat_1(X33,X32))|~v1_relat_1(X33)))&(~r2_hidden(X35,k2_relat_1(X33))|~r2_hidden(k4_tarski(X31,X35),X33)|~r2_hidden(X35,X32)|r2_hidden(X31,k10_relat_1(X33,X32))|~v1_relat_1(X33))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.17/0.52  cnf(c_0_21, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.52  cnf(c_0_22, negated_conjecture, (k8_relset_1(esk5_0,esk7_0,esk8_0,X1)=k10_relat_1(esk8_0,X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.17/0.52  cnf(c_0_23, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.52  cnf(c_0_24, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.17/0.52  cnf(c_0_25, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.17/0.52  cnf(c_0_26, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.17/0.52  cnf(c_0_27, negated_conjecture, (r2_hidden(esk10_0,esk6_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.52  cnf(c_0_28, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.52  fof(c_0_29, plain, ![X7, X8, X9, X10]:(((r2_hidden(X7,X9)|~r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)))&(r2_hidden(X8,X10)|~r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10))))&(~r2_hidden(X7,X9)|~r2_hidden(X8,X10)|r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.17/0.52  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk5_0,esk7_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_19, c_0_14])).
% 0.17/0.52  cnf(c_0_31, plain, (r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.17/0.52  cnf(c_0_32, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.52  cnf(c_0_33, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)|r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.17/0.52  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_14]), c_0_24])])).
% 0.17/0.52  cnf(c_0_35, negated_conjecture, (r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|r2_hidden(esk10_0,X1)|X1!=k2_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_25, c_0_21])).
% 0.17/0.52  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk10_0,esk6_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.17/0.52  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.17/0.52  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(esk1_3(esk8_0,X1,X2),X2),k2_zfmisc_1(esk5_0,esk7_0))|X1!=k2_relat_1(esk8_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.17/0.52  cnf(c_0_39, negated_conjecture, (r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))|r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))|~r2_hidden(esk10_0,k2_relat_1(esk8_0))|~r2_hidden(esk10_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.17/0.52  cnf(c_0_40, negated_conjecture, (r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))|r2_hidden(esk10_0,X1)|X1!=k2_relat_1(esk8_0)), inference(rw,[status(thm)],[c_0_35, c_0_22])).
% 0.17/0.52  cnf(c_0_41, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.17/0.52  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk10_0,esk6_0)|r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))), inference(rw,[status(thm)],[c_0_36, c_0_22])).
% 0.17/0.52  cnf(c_0_43, negated_conjecture, (r2_hidden(X1,esk7_0)|X2!=k2_relat_1(esk8_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.17/0.52  cnf(c_0_44, negated_conjecture, (~r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|~m1_subset_1(X1,esk7_0)|~r2_hidden(k4_tarski(esk9_0,X1),esk8_0)|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.52  cnf(c_0_45, negated_conjecture, (r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))|r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))|~r2_hidden(esk10_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.17/0.52  cnf(c_0_46, negated_conjecture, (r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))|r2_hidden(esk10_0,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_28])).
% 0.17/0.52  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,k2_relat_1(esk8_0))), inference(er,[status(thm)],[c_0_43])).
% 0.17/0.52  cnf(c_0_48, plain, (r2_hidden(esk4_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.52  cnf(c_0_49, negated_conjecture, (~m1_subset_1(X1,esk7_0)|~r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))|~r2_hidden(k4_tarski(esk9_0,X1),esk8_0)|~r2_hidden(X1,esk6_0)), inference(rw,[status(thm)],[c_0_44, c_0_22])).
% 0.17/0.52  cnf(c_0_50, negated_conjecture, (r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.17/0.52  cnf(c_0_51, negated_conjecture, (r2_hidden(esk4_3(X1,X2,esk8_0),esk7_0)|~r2_hidden(X1,k10_relat_1(esk8_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_34])])).
% 0.17/0.52  cnf(c_0_52, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.52  cnf(c_0_53, negated_conjecture, (~m1_subset_1(X1,esk7_0)|~r2_hidden(k4_tarski(esk9_0,X1),esk8_0)|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50])])).
% 0.17/0.52  cnf(c_0_54, plain, (r2_hidden(k4_tarski(X1,esk4_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.52  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk4_3(X1,X2,esk8_0),esk7_0)|~r2_hidden(X1,k10_relat_1(esk8_0,X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_51]), c_0_52])).
% 0.17/0.52  cnf(c_0_56, negated_conjecture, (~r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)|~r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_34])]), c_0_55])).
% 0.17/0.52  cnf(c_0_57, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.52  cnf(c_0_58, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_50]), c_0_34])]), ['proof']).
% 0.17/0.52  # SZS output end CNFRefutation
% 0.17/0.52  # Proof object total steps             : 59
% 0.17/0.52  # Proof object clause steps            : 40
% 0.17/0.52  # Proof object formula steps           : 19
% 0.17/0.52  # Proof object conjectures             : 30
% 0.17/0.52  # Proof object clause conjectures      : 27
% 0.17/0.52  # Proof object formula conjectures     : 3
% 0.17/0.52  # Proof object initial clauses used    : 19
% 0.17/0.52  # Proof object initial formulas used   : 9
% 0.17/0.52  # Proof object generating inferences   : 16
% 0.17/0.52  # Proof object simplifying inferences  : 21
% 0.17/0.52  # Training examples: 0 positive, 0 negative
% 0.17/0.52  # Parsed axioms                        : 9
% 0.17/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.52  # Initial clauses                      : 28
% 0.17/0.52  # Removed in clause preprocessing      : 0
% 0.17/0.52  # Initial clauses in saturation        : 28
% 0.17/0.52  # Processed clauses                    : 748
% 0.17/0.52  # ...of these trivial                  : 1
% 0.17/0.52  # ...subsumed                          : 215
% 0.17/0.52  # ...remaining for further processing  : 532
% 0.17/0.52  # Other redundant clauses eliminated   : 0
% 0.17/0.52  # Clauses deleted for lack of memory   : 0
% 0.17/0.52  # Backward-subsumed                    : 50
% 0.17/0.52  # Backward-rewritten                   : 251
% 0.17/0.52  # Generated clauses                    : 8726
% 0.17/0.52  # ...of the previous two non-trivial   : 8606
% 0.17/0.52  # Contextual simplify-reflections      : 5
% 0.17/0.52  # Paramodulations                      : 8663
% 0.17/0.52  # Factorizations                       : 2
% 0.17/0.52  # Equation resolutions                 : 61
% 0.17/0.52  # Propositional unsat checks           : 0
% 0.17/0.52  #    Propositional check models        : 0
% 0.17/0.52  #    Propositional check unsatisfiable : 0
% 0.17/0.52  #    Propositional clauses             : 0
% 0.17/0.52  #    Propositional clauses after purity: 0
% 0.17/0.52  #    Propositional unsat core size     : 0
% 0.17/0.52  #    Propositional preprocessing time  : 0.000
% 0.17/0.52  #    Propositional encoding time       : 0.000
% 0.17/0.52  #    Propositional solver time         : 0.000
% 0.17/0.52  #    Success case prop preproc time    : 0.000
% 0.17/0.52  #    Success case prop encoding time   : 0.000
% 0.17/0.52  #    Success case prop solver time     : 0.000
% 0.17/0.52  # Current number of processed clauses  : 203
% 0.17/0.52  #    Positive orientable unit clauses  : 8
% 0.17/0.52  #    Positive unorientable unit clauses: 0
% 0.17/0.52  #    Negative unit clauses             : 3
% 0.17/0.52  #    Non-unit-clauses                  : 192
% 0.17/0.52  # Current number of unprocessed clauses: 7886
% 0.17/0.52  # ...number of literals in the above   : 34140
% 0.17/0.52  # Current number of archived formulas  : 0
% 0.17/0.52  # Current number of archived clauses   : 329
% 0.17/0.52  # Clause-clause subsumption calls (NU) : 32249
% 0.17/0.52  # Rec. Clause-clause subsumption calls : 11850
% 0.17/0.52  # Non-unit clause-clause subsumptions  : 256
% 0.17/0.52  # Unit Clause-clause subsumption calls : 46
% 0.17/0.52  # Rewrite failures with RHS unbound    : 0
% 0.17/0.52  # BW rewrite match attempts            : 3
% 0.17/0.52  # BW rewrite match successes           : 3
% 0.17/0.52  # Condensation attempts                : 0
% 0.17/0.52  # Condensation successes               : 0
% 0.17/0.52  # Termbank termtop insertions          : 181478
% 0.17/0.52  
% 0.17/0.52  # -------------------------------------------------
% 0.17/0.52  # User time                : 0.190 s
% 0.17/0.52  # System time              : 0.013 s
% 0.17/0.52  # Total time               : 0.203 s
% 0.17/0.52  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
