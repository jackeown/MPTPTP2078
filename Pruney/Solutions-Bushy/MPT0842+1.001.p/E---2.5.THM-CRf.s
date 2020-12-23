%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0842+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:17 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 185 expanded)
%              Number of clauses        :   43 (  80 expanded)
%              Number of leaves         :   10 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  208 (1045 expanded)
%              Number of equality atoms :   22 (  69 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X24,X25,X26,X27] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | k8_relset_1(X24,X25,X26,X27) = k10_relat_1(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_12,negated_conjecture,(
    ! [X46] :
      ( ~ v1_xboole_0(esk5_0)
      & ~ v1_xboole_0(esk6_0)
      & ~ v1_xboole_0(esk7_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))
      & m1_subset_1(esk9_0,esk5_0)
      & ( ~ r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
        | ~ m1_subset_1(X46,esk7_0)
        | ~ r2_hidden(k4_tarski(esk9_0,X46),esk8_0)
        | ~ r2_hidden(X46,esk6_0) )
      & ( m1_subset_1(esk10_0,esk7_0)
        | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) )
      & ( r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)
        | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) )
      & ( r2_hidden(esk10_0,esk6_0)
        | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).

cnf(c_0_13,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_16,plain,(
    ! [X10,X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( r2_hidden(k4_tarski(X13,esk1_4(X10,X11,X12,X13)),X10)
        | ~ r2_hidden(X13,X12)
        | X12 != k10_relat_1(X10,X11)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk1_4(X10,X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k10_relat_1(X10,X11)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(k4_tarski(X15,X16),X10)
        | ~ r2_hidden(X16,X11)
        | r2_hidden(X15,X12)
        | X12 != k10_relat_1(X10,X11)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(esk2_3(X10,X17,X18),X18)
        | ~ r2_hidden(k4_tarski(esk2_3(X10,X17,X18),X20),X10)
        | ~ r2_hidden(X20,X17)
        | X18 = k10_relat_1(X10,X17)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(esk2_3(X10,X17,X18),esk3_3(X10,X17,X18)),X10)
        | r2_hidden(esk2_3(X10,X17,X18),X18)
        | X18 = k10_relat_1(X10,X17)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk3_3(X10,X17,X18),X17)
        | r2_hidden(esk2_3(X10,X17,X18),X18)
        | X18 = k10_relat_1(X10,X17)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)
    | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k8_relset_1(esk5_0,esk7_0,esk8_0,X1) = k10_relat_1(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)
    | r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))
    | r2_hidden(esk9_0,X1)
    | X1 != k10_relat_1(esk8_0,X2)
    | ~ r2_hidden(esk10_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk10_0,esk6_0)
    | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | ~ m1_subset_1(X1,esk7_0)
    | ~ r2_hidden(k4_tarski(esk9_0,X1),esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))
    | r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))
    | ~ r2_hidden(esk10_0,X1) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))
    | r2_hidden(esk10_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_18])).

fof(c_0_28,plain,(
    ! [X36,X37,X38] :
      ( ~ r2_hidden(X36,X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X38))
      | m1_subset_1(X36,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))
    | ~ r2_hidden(k4_tarski(esk9_0,X1),esk8_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,esk7_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk9_0,X1),esk8_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,X4,X1)),X2)
    | ~ r2_hidden(X1,X4)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_34,plain,(
    ! [X32,X33] :
      ( ~ r2_hidden(X32,X33)
      | m1_subset_1(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_35,plain,(
    ! [X34,X35] :
      ( ~ m1_subset_1(X34,X35)
      | v1_xboole_0(X35)
      | r2_hidden(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(esk5_0,esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( X1 != k10_relat_1(esk8_0,X2)
    | ~ r2_hidden(esk1_4(esk8_0,X2,X1,esk9_0),esk6_0)
    | ~ r2_hidden(esk9_0,X1)
    | ~ m1_subset_1(esk1_4(esk8_0,X2,X1,esk9_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_22])])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_39,plain,(
    ! [X28,X29,X30,X31] :
      ( ( r2_hidden(X28,X30)
        | ~ r2_hidden(k4_tarski(X28,X29),k2_zfmisc_1(X30,X31)) )
      & ( r2_hidden(X29,X31)
        | ~ r2_hidden(k4_tarski(X28,X29),k2_zfmisc_1(X30,X31)) )
      & ( ~ r2_hidden(X28,X30)
        | ~ r2_hidden(X29,X31)
        | r2_hidden(k4_tarski(X28,X29),k2_zfmisc_1(X30,X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k4_tarski(X1,esk1_4(esk8_0,X2,X3,X1)),k2_zfmisc_1(esk5_0,esk7_0))
    | X3 != k10_relat_1(esk8_0,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_33]),c_0_22])])).

cnf(c_0_42,negated_conjecture,
    ( X1 != k10_relat_1(esk8_0,X2)
    | ~ r2_hidden(esk1_4(esk8_0,X2,X1,esk9_0),esk6_0)
    | ~ r2_hidden(esk1_4(esk8_0,X2,X1,esk9_0),esk7_0)
    | ~ r2_hidden(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk5_0,esk7_0))
    | r2_hidden(k4_tarski(X1,esk1_4(esk8_0,X2,X3,X1)),k2_zfmisc_1(esk5_0,esk7_0))
    | X3 != k10_relat_1(esk8_0,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_46,plain,(
    ! [X39,X40] :
      ( ~ r2_hidden(X39,X40)
      | ~ v1_xboole_0(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_47,negated_conjecture,
    ( X1 != k10_relat_1(esk8_0,esk6_0)
    | ~ r2_hidden(esk1_4(esk8_0,esk6_0,X1,esk9_0),esk7_0)
    | ~ r2_hidden(esk9_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_22])])).

cnf(c_0_48,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk5_0,esk7_0))
    | r2_hidden(esk1_4(esk8_0,X1,X2,X3),esk7_0)
    | X2 != k10_relat_1(esk8_0,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_50,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk5_0,esk7_0))
    | X1 != k10_relat_1(esk8_0,esk6_0)
    | ~ r2_hidden(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_52,plain,(
    ! [X22] : m1_subset_1(esk4_1(X22),X22) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_53,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_51]),c_0_30])])).

cnf(c_0_55,plain,
    ( m1_subset_1(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk9_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk5_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk4_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk9_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_56]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_61,c_0_62]),
    [proof]).

%------------------------------------------------------------------------------
