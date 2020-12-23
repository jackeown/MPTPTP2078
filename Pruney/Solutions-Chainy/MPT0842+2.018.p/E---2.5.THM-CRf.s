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
% DateTime   : Thu Dec  3 10:58:47 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 166 expanded)
%              Number of clauses        :   30 (  69 expanded)
%              Number of leaves         :    9 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  199 ( 910 expanded)
%              Number of equality atoms :   13 (  38 expanded)
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

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

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

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

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
    ! [X37,X38,X39,X40] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k8_relset_1(X37,X38,X39,X40) = k10_relat_1(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_11,negated_conjecture,(
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
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).

cnf(c_0_12,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | v1_relat_1(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_15,plain,(
    ! [X30,X31] : v1_relat_1(k2_zfmisc_1(X30,X31)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_16,plain,(
    ! [X18,X19,X20,X21,X23,X24,X25,X26,X28] :
      ( ( r2_hidden(k4_tarski(X21,esk1_4(X18,X19,X20,X21)),X18)
        | ~ r2_hidden(X21,X20)
        | X20 != k10_relat_1(X18,X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(esk1_4(X18,X19,X20,X21),X19)
        | ~ r2_hidden(X21,X20)
        | X20 != k10_relat_1(X18,X19)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X23,X24),X18)
        | ~ r2_hidden(X24,X19)
        | r2_hidden(X23,X20)
        | X20 != k10_relat_1(X18,X19)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(esk2_3(X18,X25,X26),X26)
        | ~ r2_hidden(k4_tarski(esk2_3(X18,X25,X26),X28),X18)
        | ~ r2_hidden(X28,X25)
        | X26 = k10_relat_1(X18,X25)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk2_3(X18,X25,X26),esk3_3(X18,X25,X26)),X18)
        | r2_hidden(esk2_3(X18,X25,X26),X26)
        | X26 = k10_relat_1(X18,X25)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(esk3_3(X18,X25,X26),X25)
        | r2_hidden(esk2_3(X18,X25,X26),X26)
        | X26 = k10_relat_1(X18,X25)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)
    | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k8_relset_1(esk5_0,esk7_0,esk8_0,X1) = k10_relat_1(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)
    | r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_13]),c_0_20])])).

fof(c_0_24,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | ~ r2_hidden(X15,X14)
      | r2_hidden(X15,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))
    | r2_hidden(esk9_0,X1)
    | X1 != k10_relat_1(esk8_0,X2)
    | ~ r2_hidden(esk10_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk10_0,esk6_0)
    | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X32,X33,X34,X36] :
      ( ( r2_hidden(esk4_3(X32,X33,X34),k2_relat_1(X34))
        | ~ r2_hidden(X32,k10_relat_1(X34,X33))
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(k4_tarski(X32,esk4_3(X32,X33,X34)),X34)
        | ~ r2_hidden(X32,k10_relat_1(X34,X33))
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(esk4_3(X32,X33,X34),X33)
        | ~ r2_hidden(X32,k10_relat_1(X34,X33))
        | ~ v1_relat_1(X34) )
      & ( ~ r2_hidden(X36,k2_relat_1(X34))
        | ~ r2_hidden(k4_tarski(X32,X36),X34)
        | ~ r2_hidden(X36,X33)
        | r2_hidden(X32,k10_relat_1(X34,X33))
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))
    | ~ m1_subset_1(X1,esk7_0)
    | ~ r2_hidden(k4_tarski(esk9_0,X1),esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))
    | r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))
    | ~ r2_hidden(esk10_0,X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))
    | r2_hidden(esk10_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_18])).

fof(c_0_32,plain,(
    ! [X7,X8,X9,X10] :
      ( ( r2_hidden(X7,X9)
        | ~ r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)) )
      & ( r2_hidden(X8,X10)
        | ~ r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)) )
      & ( ~ r2_hidden(X7,X9)
        | ~ r2_hidden(X8,X10)
        | r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk5_0,esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_13])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( ~ m1_subset_1(X1,esk7_0)
    | ~ r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))
    | ~ r2_hidden(k4_tarski(esk9_0,X1),esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_37,plain,(
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

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk4_3(X1,X2,esk8_0)),k2_zfmisc_1(esk5_0,esk7_0))
    | ~ r2_hidden(X1,k10_relat_1(esk8_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_23])])).

cnf(c_0_40,negated_conjecture,
    ( ~ m1_subset_1(X1,esk7_0)
    | ~ r2_hidden(k4_tarski(esk9_0,X1),esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk4_3(X1,X2,esk8_0),esk7_0)
    | ~ r2_hidden(X1,k10_relat_1(esk8_0,X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( ~ m1_subset_1(esk4_3(esk9_0,X1,esk8_0),esk7_0)
    | ~ r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)
    | ~ r2_hidden(esk9_0,k10_relat_1(esk8_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_34]),c_0_23])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk4_3(X1,X2,esk8_0),esk7_0)
    | ~ r2_hidden(X1,k10_relat_1(esk8_0,X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)
    | ~ r2_hidden(esk9_0,k10_relat_1(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_47,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_36]),c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.19/0.43  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.041 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(t53_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k8_relset_1(X1,X3,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X5,X6),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_relset_1)).
% 0.19/0.43  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.19/0.43  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.43  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.43  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 0.19/0.43  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.43  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.19/0.43  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.19/0.43  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.43  fof(c_0_9, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k8_relset_1(X1,X3,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X5,X6),X4))&r2_hidden(X6,X2))))))))), inference(assume_negation,[status(cth)],[t53_relset_1])).
% 0.19/0.43  fof(c_0_10, plain, ![X37, X38, X39, X40]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k8_relset_1(X37,X38,X39,X40)=k10_relat_1(X39,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.19/0.43  fof(c_0_11, negated_conjecture, ![X46]:(~v1_xboole_0(esk5_0)&(~v1_xboole_0(esk6_0)&(~v1_xboole_0(esk7_0)&(m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))&(m1_subset_1(esk9_0,esk5_0)&((~r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|(~m1_subset_1(X46,esk7_0)|~r2_hidden(k4_tarski(esk9_0,X46),esk8_0)|~r2_hidden(X46,esk6_0)))&(((m1_subset_1(esk10_0,esk7_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)))&(r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))))&(r2_hidden(esk10_0,esk6_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0)))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).
% 0.19/0.43  cnf(c_0_12, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.43  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.43  fof(c_0_14, plain, ![X16, X17]:(~v1_relat_1(X16)|(~m1_subset_1(X17,k1_zfmisc_1(X16))|v1_relat_1(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.43  fof(c_0_15, plain, ![X30, X31]:v1_relat_1(k2_zfmisc_1(X30,X31)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.43  fof(c_0_16, plain, ![X18, X19, X20, X21, X23, X24, X25, X26, X28]:((((r2_hidden(k4_tarski(X21,esk1_4(X18,X19,X20,X21)),X18)|~r2_hidden(X21,X20)|X20!=k10_relat_1(X18,X19)|~v1_relat_1(X18))&(r2_hidden(esk1_4(X18,X19,X20,X21),X19)|~r2_hidden(X21,X20)|X20!=k10_relat_1(X18,X19)|~v1_relat_1(X18)))&(~r2_hidden(k4_tarski(X23,X24),X18)|~r2_hidden(X24,X19)|r2_hidden(X23,X20)|X20!=k10_relat_1(X18,X19)|~v1_relat_1(X18)))&((~r2_hidden(esk2_3(X18,X25,X26),X26)|(~r2_hidden(k4_tarski(esk2_3(X18,X25,X26),X28),X18)|~r2_hidden(X28,X25))|X26=k10_relat_1(X18,X25)|~v1_relat_1(X18))&((r2_hidden(k4_tarski(esk2_3(X18,X25,X26),esk3_3(X18,X25,X26)),X18)|r2_hidden(esk2_3(X18,X25,X26),X26)|X26=k10_relat_1(X18,X25)|~v1_relat_1(X18))&(r2_hidden(esk3_3(X18,X25,X26),X25)|r2_hidden(esk2_3(X18,X25,X26),X26)|X26=k10_relat_1(X18,X25)|~v1_relat_1(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.19/0.43  cnf(c_0_17, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.43  cnf(c_0_18, negated_conjecture, (k8_relset_1(esk5_0,esk7_0,esk8_0,X1)=k10_relat_1(esk8_0,X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.43  cnf(c_0_19, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.43  cnf(c_0_20, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.43  cnf(c_0_21, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.43  cnf(c_0_22, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk10_0),esk8_0)|r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.43  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_13]), c_0_20])])).
% 0.19/0.43  fof(c_0_24, plain, ![X13, X14, X15]:(~m1_subset_1(X14,k1_zfmisc_1(X13))|(~r2_hidden(X15,X14)|r2_hidden(X15,X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.43  cnf(c_0_25, negated_conjecture, (r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))|r2_hidden(esk9_0,X1)|X1!=k10_relat_1(esk8_0,X2)|~r2_hidden(esk10_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.19/0.43  cnf(c_0_26, negated_conjecture, (r2_hidden(esk10_0,esk6_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.43  cnf(c_0_27, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.43  fof(c_0_28, plain, ![X32, X33, X34, X36]:((((r2_hidden(esk4_3(X32,X33,X34),k2_relat_1(X34))|~r2_hidden(X32,k10_relat_1(X34,X33))|~v1_relat_1(X34))&(r2_hidden(k4_tarski(X32,esk4_3(X32,X33,X34)),X34)|~r2_hidden(X32,k10_relat_1(X34,X33))|~v1_relat_1(X34)))&(r2_hidden(esk4_3(X32,X33,X34),X33)|~r2_hidden(X32,k10_relat_1(X34,X33))|~v1_relat_1(X34)))&(~r2_hidden(X36,k2_relat_1(X34))|~r2_hidden(k4_tarski(X32,X36),X34)|~r2_hidden(X36,X33)|r2_hidden(X32,k10_relat_1(X34,X33))|~v1_relat_1(X34))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.19/0.43  cnf(c_0_29, negated_conjecture, (~r2_hidden(esk9_0,k8_relset_1(esk5_0,esk7_0,esk8_0,esk6_0))|~m1_subset_1(X1,esk7_0)|~r2_hidden(k4_tarski(esk9_0,X1),esk8_0)|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.43  cnf(c_0_30, negated_conjecture, (r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))|r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))|~r2_hidden(esk10_0,X1)), inference(er,[status(thm)],[c_0_25])).
% 0.19/0.43  cnf(c_0_31, negated_conjecture, (r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))|r2_hidden(esk10_0,esk6_0)), inference(rw,[status(thm)],[c_0_26, c_0_18])).
% 0.19/0.43  fof(c_0_32, plain, ![X7, X8, X9, X10]:(((r2_hidden(X7,X9)|~r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)))&(r2_hidden(X8,X10)|~r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10))))&(~r2_hidden(X7,X9)|~r2_hidden(X8,X10)|r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.19/0.43  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk5_0,esk7_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_27, c_0_13])).
% 0.19/0.43  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X1,esk4_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.43  cnf(c_0_35, negated_conjecture, (~m1_subset_1(X1,esk7_0)|~r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))|~r2_hidden(k4_tarski(esk9_0,X1),esk8_0)|~r2_hidden(X1,esk6_0)), inference(rw,[status(thm)],[c_0_29, c_0_18])).
% 0.19/0.43  cnf(c_0_36, negated_conjecture, (r2_hidden(esk9_0,k10_relat_1(esk8_0,esk6_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.43  fof(c_0_37, plain, ![X11, X12]:(((~m1_subset_1(X12,X11)|r2_hidden(X12,X11)|v1_xboole_0(X11))&(~r2_hidden(X12,X11)|m1_subset_1(X12,X11)|v1_xboole_0(X11)))&((~m1_subset_1(X12,X11)|v1_xboole_0(X12)|~v1_xboole_0(X11))&(~v1_xboole_0(X12)|m1_subset_1(X12,X11)|~v1_xboole_0(X11)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.43  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.43  cnf(c_0_39, negated_conjecture, (r2_hidden(k4_tarski(X1,esk4_3(X1,X2,esk8_0)),k2_zfmisc_1(esk5_0,esk7_0))|~r2_hidden(X1,k10_relat_1(esk8_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_23])])).
% 0.19/0.43  cnf(c_0_40, negated_conjecture, (~m1_subset_1(X1,esk7_0)|~r2_hidden(k4_tarski(esk9_0,X1),esk8_0)|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])])).
% 0.19/0.43  cnf(c_0_41, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.43  cnf(c_0_42, negated_conjecture, (r2_hidden(esk4_3(X1,X2,esk8_0),esk7_0)|~r2_hidden(X1,k10_relat_1(esk8_0,X2))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.43  cnf(c_0_43, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.43  cnf(c_0_44, negated_conjecture, (~m1_subset_1(esk4_3(esk9_0,X1,esk8_0),esk7_0)|~r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)|~r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_34]), c_0_23])])).
% 0.19/0.43  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk4_3(X1,X2,esk8_0),esk7_0)|~r2_hidden(X1,k10_relat_1(esk8_0,X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.19/0.43  cnf(c_0_46, negated_conjecture, (~r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)|~r2_hidden(esk9_0,k10_relat_1(esk8_0,X1))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.43  cnf(c_0_47, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.43  cnf(c_0_48, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_36]), c_0_23])]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 49
% 0.19/0.43  # Proof object clause steps            : 30
% 0.19/0.43  # Proof object formula steps           : 19
% 0.19/0.43  # Proof object conjectures             : 24
% 0.19/0.43  # Proof object clause conjectures      : 21
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 14
% 0.19/0.43  # Proof object initial formulas used   : 9
% 0.19/0.43  # Proof object generating inferences   : 12
% 0.19/0.43  # Proof object simplifying inferences  : 17
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 9
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 30
% 0.19/0.43  # Removed in clause preprocessing      : 0
% 0.19/0.43  # Initial clauses in saturation        : 30
% 0.19/0.43  # Processed clauses                    : 306
% 0.19/0.43  # ...of these trivial                  : 0
% 0.19/0.43  # ...subsumed                          : 90
% 0.19/0.43  # ...remaining for further processing  : 216
% 0.19/0.43  # Other redundant clauses eliminated   : 0
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 6
% 0.19/0.43  # Backward-rewritten                   : 42
% 0.19/0.43  # Generated clauses                    : 773
% 0.19/0.43  # ...of the previous two non-trivial   : 727
% 0.19/0.43  # Contextual simplify-reflections      : 1
% 0.19/0.43  # Paramodulations                      : 760
% 0.19/0.43  # Factorizations                       : 0
% 0.19/0.43  # Equation resolutions                 : 13
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
% 0.19/0.43  # Current number of processed clauses  : 138
% 0.19/0.43  #    Positive orientable unit clauses  : 7
% 0.19/0.43  #    Positive unorientable unit clauses: 0
% 0.19/0.43  #    Negative unit clauses             : 3
% 0.19/0.43  #    Non-unit-clauses                  : 128
% 0.19/0.43  # Current number of unprocessed clauses: 432
% 0.19/0.43  # ...number of literals in the above   : 1848
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 78
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 3395
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 1470
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 91
% 0.19/0.43  # Unit Clause-clause subsumption calls : 19
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 2
% 0.19/0.43  # BW rewrite match successes           : 2
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 19802
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.086 s
% 0.19/0.43  # System time              : 0.006 s
% 0.19/0.43  # Total time               : 0.092 s
% 0.19/0.43  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
