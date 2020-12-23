%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:42 EST 2020

% Result     : Theorem 43.90s
% Output     : CNFRefutation 43.90s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 206 expanded)
%              Number of clauses        :   37 (  85 expanded)
%              Number of leaves         :   11 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  226 (1205 expanded)
%              Number of equality atoms :   19 (  49 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
                      <=> ? [X6] :
                            ( m1_subset_1(X6,X3)
                            & r2_hidden(k4_tarski(X6,X5),X4)
                            & r2_hidden(X6,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(d13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ~ v1_xboole_0(X3)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
                        <=> ? [X6] :
                              ( m1_subset_1(X6,X3)
                              & r2_hidden(k4_tarski(X6,X5),X4)
                              & r2_hidden(X6,X2) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relset_1])).

fof(c_0_12,plain,(
    ! [X18,X19,X20] :
      ( ~ r2_hidden(X18,X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X20))
      | ~ v1_xboole_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_13,negated_conjecture,(
    ! [X61] :
      ( ~ v1_xboole_0(esk8_0)
      & ~ v1_xboole_0(esk9_0)
      & ~ v1_xboole_0(esk10_0)
      & m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk8_0)))
      & m1_subset_1(esk12_0,esk8_0)
      & ( ~ r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))
        | ~ m1_subset_1(X61,esk10_0)
        | ~ r2_hidden(k4_tarski(X61,esk12_0),esk11_0)
        | ~ r2_hidden(X61,esk9_0) )
      & ( m1_subset_1(esk13_0,esk10_0)
        | r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0)) )
      & ( r2_hidden(k4_tarski(esk13_0,esk12_0),esk11_0)
        | r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0)) )
      & ( r2_hidden(esk13_0,esk9_0)
        | r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])])).

fof(c_0_14,plain,(
    ! [X49,X50,X51] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | v1_relat_1(X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X33,X34,X35,X37,X38,X39,X40,X42] :
      ( ( ~ r2_hidden(X35,X34)
        | r2_hidden(k4_tarski(X35,esk4_3(X33,X34,X35)),X33)
        | X34 != k1_relat_1(X33) )
      & ( ~ r2_hidden(k4_tarski(X37,X38),X33)
        | r2_hidden(X37,X34)
        | X34 != k1_relat_1(X33) )
      & ( ~ r2_hidden(esk5_2(X39,X40),X40)
        | ~ r2_hidden(k4_tarski(esk5_2(X39,X40),X42),X39)
        | X40 = k1_relat_1(X39) )
      & ( r2_hidden(esk5_2(X39,X40),X40)
        | r2_hidden(k4_tarski(esk5_2(X39,X40),esk6_2(X39,X40)),X39)
        | X40 = k1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_18,plain,(
    ! [X21,X22,X23,X24,X26,X27,X28,X29,X31] :
      ( ( r2_hidden(k4_tarski(esk1_4(X21,X22,X23,X24),X24),X21)
        | ~ r2_hidden(X24,X23)
        | X23 != k9_relat_1(X21,X22)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(esk1_4(X21,X22,X23,X24),X22)
        | ~ r2_hidden(X24,X23)
        | X23 != k9_relat_1(X21,X22)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(X27,X26),X21)
        | ~ r2_hidden(X27,X22)
        | r2_hidden(X26,X23)
        | X23 != k9_relat_1(X21,X22)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(esk2_3(X21,X28,X29),X29)
        | ~ r2_hidden(k4_tarski(X31,esk2_3(X21,X28,X29)),X21)
        | ~ r2_hidden(X31,X28)
        | X29 = k9_relat_1(X21,X28)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(esk3_3(X21,X28,X29),esk2_3(X21,X28,X29)),X21)
        | r2_hidden(esk2_3(X21,X28,X29),X29)
        | X29 = k9_relat_1(X21,X28)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(esk3_3(X21,X28,X29),X28)
        | r2_hidden(esk2_3(X21,X28,X29),X29)
        | X29 = k9_relat_1(X21,X28)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

cnf(c_0_19,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk10_0,esk8_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X2,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X5 != k9_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(esk13_0,esk12_0),esk11_0)
    | r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_16])).

fof(c_0_25,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X17))
      | m1_subset_1(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_26,negated_conjecture,
    ( X1 != k1_relat_1(esk11_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk10_0,esk8_0))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_27,plain,(
    ! [X44,X45,X46,X48] :
      ( ( r2_hidden(esk7_3(X44,X45,X46),k1_relat_1(X46))
        | ~ r2_hidden(X44,k9_relat_1(X46,X45))
        | ~ v1_relat_1(X46) )
      & ( r2_hidden(k4_tarski(esk7_3(X44,X45,X46),X44),X46)
        | ~ r2_hidden(X44,k9_relat_1(X46,X45))
        | ~ v1_relat_1(X46) )
      & ( r2_hidden(esk7_3(X44,X45,X46),X45)
        | ~ r2_hidden(X44,k9_relat_1(X46,X45))
        | ~ v1_relat_1(X46) )
      & ( ~ r2_hidden(X48,k1_relat_1(X46))
        | ~ r2_hidden(k4_tarski(X48,X44),X46)
        | ~ r2_hidden(X48,X45)
        | r2_hidden(X44,k9_relat_1(X46,X45))
        | ~ v1_relat_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_28,plain,(
    ! [X52,X53,X54,X55] :
      ( ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | k7_relset_1(X52,X53,X54,X55) = k9_relat_1(X54,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))
    | r2_hidden(esk12_0,X1)
    | X1 != k9_relat_1(esk11_0,X2)
    | ~ r2_hidden(esk13_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk10_0,esk8_0))
    | ~ r2_hidden(X1,k1_relat_1(esk11_0)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))
    | ~ v1_xboole_0(k2_zfmisc_1(esk10_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_23])).

cnf(c_0_34,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))
    | ~ m1_subset_1(X1,esk10_0)
    | ~ r2_hidden(k4_tarski(X1,esk12_0),esk11_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(esk7_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X11,X12] :
      ( ~ r2_hidden(X11,X12)
      | m1_subset_1(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))
    | r2_hidden(esk12_0,k9_relat_1(esk11_0,X1))
    | ~ r2_hidden(esk13_0,X1) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk13_0,esk9_0)
    | r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_40,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X13,X14)
      | v1_xboole_0(X14)
      | r2_hidden(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(esk10_0,esk8_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk10_0,esk8_0))
    | ~ r2_hidden(X1,k9_relat_1(esk11_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_24])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk12_0,k9_relat_1(esk11_0,esk9_0))
    | ~ v1_xboole_0(k2_zfmisc_1(esk10_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_16])])).

cnf(c_0_44,negated_conjecture,
    ( ~ m1_subset_1(esk7_3(esk12_0,X1,esk11_0),esk10_0)
    | ~ r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))
    | ~ r2_hidden(esk7_3(esk12_0,X1,esk11_0),esk9_0)
    | ~ r2_hidden(esk12_0,k9_relat_1(esk11_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_24])])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))
    | r2_hidden(esk12_0,k9_relat_1(esk11_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_47,plain,(
    ! [X7,X8,X9,X10] :
      ( ( r2_hidden(X7,X9)
        | ~ r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)) )
      & ( r2_hidden(X8,X10)
        | ~ r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)) )
      & ( ~ r2_hidden(X7,X9)
        | ~ r2_hidden(X8,X10)
        | r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k4_tarski(esk7_3(X1,X2,esk11_0),X1),k2_zfmisc_1(esk10_0,esk8_0))
    | ~ r2_hidden(X1,k9_relat_1(esk11_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_36]),c_0_24])])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk10_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))
    | ~ r2_hidden(esk7_3(esk12_0,X1,esk11_0),esk9_0)
    | ~ r2_hidden(esk7_3(esk12_0,X1,esk11_0),esk10_0)
    | ~ r2_hidden(esk12_0,k9_relat_1(esk11_0,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk12_0,k9_relat_1(esk11_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_34]),c_0_16])])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_3(X1,X2,esk11_0),X1),k2_zfmisc_1(esk10_0,esk8_0))
    | ~ r2_hidden(X1,k9_relat_1(esk11_0,X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))
    | ~ r2_hidden(esk7_3(esk12_0,esk9_0,esk11_0),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_24])])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk7_3(X1,X2,esk11_0),esk10_0)
    | ~ r2_hidden(X1,k9_relat_1(esk11_0,X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_53])])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_34]),c_0_53]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n012.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 12:21:22 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 43.90/44.08  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 43.90/44.08  # and selection function SelectMaxLComplexAvoidPosPred.
% 43.90/44.08  #
% 43.90/44.08  # Preprocessing time       : 0.029 s
% 43.90/44.08  # Presaturation interreduction done
% 43.90/44.08  
% 43.90/44.08  # Proof found!
% 43.90/44.08  # SZS status Theorem
% 43.90/44.08  # SZS output start CNFRefutation
% 43.90/44.08  fof(t52_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 43.90/44.08  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 43.90/44.08  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 43.90/44.08  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 43.90/44.08  fof(d13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X5,X4),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 43.90/44.08  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 43.90/44.08  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 43.90/44.08  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 43.90/44.08  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 43.90/44.08  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 43.90/44.08  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 43.90/44.08  fof(c_0_11, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2))))))))), inference(assume_negation,[status(cth)],[t52_relset_1])).
% 43.90/44.08  fof(c_0_12, plain, ![X18, X19, X20]:(~r2_hidden(X18,X19)|~m1_subset_1(X19,k1_zfmisc_1(X20))|~v1_xboole_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 43.90/44.08  fof(c_0_13, negated_conjecture, ![X61]:(~v1_xboole_0(esk8_0)&(~v1_xboole_0(esk9_0)&(~v1_xboole_0(esk10_0)&(m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk8_0)))&(m1_subset_1(esk12_0,esk8_0)&((~r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))|(~m1_subset_1(X61,esk10_0)|~r2_hidden(k4_tarski(X61,esk12_0),esk11_0)|~r2_hidden(X61,esk9_0)))&(((m1_subset_1(esk13_0,esk10_0)|r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0)))&(r2_hidden(k4_tarski(esk13_0,esk12_0),esk11_0)|r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))))&(r2_hidden(esk13_0,esk9_0)|r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0)))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])])).
% 43.90/44.08  fof(c_0_14, plain, ![X49, X50, X51]:(~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|v1_relat_1(X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 43.90/44.08  cnf(c_0_15, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 43.90/44.08  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 43.90/44.08  fof(c_0_17, plain, ![X33, X34, X35, X37, X38, X39, X40, X42]:(((~r2_hidden(X35,X34)|r2_hidden(k4_tarski(X35,esk4_3(X33,X34,X35)),X33)|X34!=k1_relat_1(X33))&(~r2_hidden(k4_tarski(X37,X38),X33)|r2_hidden(X37,X34)|X34!=k1_relat_1(X33)))&((~r2_hidden(esk5_2(X39,X40),X40)|~r2_hidden(k4_tarski(esk5_2(X39,X40),X42),X39)|X40=k1_relat_1(X39))&(r2_hidden(esk5_2(X39,X40),X40)|r2_hidden(k4_tarski(esk5_2(X39,X40),esk6_2(X39,X40)),X39)|X40=k1_relat_1(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 43.90/44.08  fof(c_0_18, plain, ![X21, X22, X23, X24, X26, X27, X28, X29, X31]:((((r2_hidden(k4_tarski(esk1_4(X21,X22,X23,X24),X24),X21)|~r2_hidden(X24,X23)|X23!=k9_relat_1(X21,X22)|~v1_relat_1(X21))&(r2_hidden(esk1_4(X21,X22,X23,X24),X22)|~r2_hidden(X24,X23)|X23!=k9_relat_1(X21,X22)|~v1_relat_1(X21)))&(~r2_hidden(k4_tarski(X27,X26),X21)|~r2_hidden(X27,X22)|r2_hidden(X26,X23)|X23!=k9_relat_1(X21,X22)|~v1_relat_1(X21)))&((~r2_hidden(esk2_3(X21,X28,X29),X29)|(~r2_hidden(k4_tarski(X31,esk2_3(X21,X28,X29)),X21)|~r2_hidden(X31,X28))|X29=k9_relat_1(X21,X28)|~v1_relat_1(X21))&((r2_hidden(k4_tarski(esk3_3(X21,X28,X29),esk2_3(X21,X28,X29)),X21)|r2_hidden(esk2_3(X21,X28,X29),X29)|X29=k9_relat_1(X21,X28)|~v1_relat_1(X21))&(r2_hidden(esk3_3(X21,X28,X29),X28)|r2_hidden(esk2_3(X21,X28,X29),X29)|X29=k9_relat_1(X21,X28)|~v1_relat_1(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).
% 43.90/44.08  cnf(c_0_19, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 43.90/44.08  cnf(c_0_20, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk10_0,esk8_0))|~r2_hidden(X1,esk11_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 43.90/44.08  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 43.90/44.08  cnf(c_0_22, plain, (r2_hidden(X2,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X5!=k9_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 43.90/44.08  cnf(c_0_23, negated_conjecture, (r2_hidden(k4_tarski(esk13_0,esk12_0),esk11_0)|r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 43.90/44.08  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk11_0)), inference(spm,[status(thm)],[c_0_19, c_0_16])).
% 43.90/44.08  fof(c_0_25, plain, ![X15, X16, X17]:(~r2_hidden(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X17))|m1_subset_1(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 43.90/44.08  cnf(c_0_26, negated_conjecture, (X1!=k1_relat_1(esk11_0)|~v1_xboole_0(k2_zfmisc_1(esk10_0,esk8_0))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 43.90/44.08  fof(c_0_27, plain, ![X44, X45, X46, X48]:((((r2_hidden(esk7_3(X44,X45,X46),k1_relat_1(X46))|~r2_hidden(X44,k9_relat_1(X46,X45))|~v1_relat_1(X46))&(r2_hidden(k4_tarski(esk7_3(X44,X45,X46),X44),X46)|~r2_hidden(X44,k9_relat_1(X46,X45))|~v1_relat_1(X46)))&(r2_hidden(esk7_3(X44,X45,X46),X45)|~r2_hidden(X44,k9_relat_1(X46,X45))|~v1_relat_1(X46)))&(~r2_hidden(X48,k1_relat_1(X46))|~r2_hidden(k4_tarski(X48,X44),X46)|~r2_hidden(X48,X45)|r2_hidden(X44,k9_relat_1(X46,X45))|~v1_relat_1(X46))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 43.90/44.08  fof(c_0_28, plain, ![X52, X53, X54, X55]:(~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|k7_relset_1(X52,X53,X54,X55)=k9_relat_1(X54,X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 43.90/44.08  cnf(c_0_29, negated_conjecture, (r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))|r2_hidden(esk12_0,X1)|X1!=k9_relat_1(esk11_0,X2)|~r2_hidden(esk13_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 43.90/44.08  cnf(c_0_30, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 43.90/44.08  cnf(c_0_31, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk10_0,esk8_0))|~r2_hidden(X1,k1_relat_1(esk11_0))), inference(er,[status(thm)],[c_0_26])).
% 43.90/44.08  cnf(c_0_32, plain, (r2_hidden(esk7_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 43.90/44.08  cnf(c_0_33, negated_conjecture, (r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))|~v1_xboole_0(k2_zfmisc_1(esk10_0,esk8_0))), inference(spm,[status(thm)],[c_0_20, c_0_23])).
% 43.90/44.08  cnf(c_0_34, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 43.90/44.08  cnf(c_0_35, negated_conjecture, (~r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))|~m1_subset_1(X1,esk10_0)|~r2_hidden(k4_tarski(X1,esk12_0),esk11_0)|~r2_hidden(X1,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 43.90/44.08  cnf(c_0_36, plain, (r2_hidden(k4_tarski(esk7_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 43.90/44.08  fof(c_0_37, plain, ![X11, X12]:(~r2_hidden(X11,X12)|m1_subset_1(X11,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 43.90/44.08  cnf(c_0_38, negated_conjecture, (r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))|r2_hidden(esk12_0,k9_relat_1(esk11_0,X1))|~r2_hidden(esk13_0,X1)), inference(er,[status(thm)],[c_0_29])).
% 43.90/44.08  cnf(c_0_39, negated_conjecture, (r2_hidden(esk13_0,esk9_0)|r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 43.90/44.08  fof(c_0_40, plain, ![X13, X14]:(~m1_subset_1(X13,X14)|(v1_xboole_0(X14)|r2_hidden(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 43.90/44.08  cnf(c_0_41, negated_conjecture, (m1_subset_1(X1,k2_zfmisc_1(esk10_0,esk8_0))|~r2_hidden(X1,esk11_0)), inference(spm,[status(thm)],[c_0_30, c_0_16])).
% 43.90/44.08  cnf(c_0_42, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk10_0,esk8_0))|~r2_hidden(X1,k9_relat_1(esk11_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_24])])).
% 43.90/44.08  cnf(c_0_43, negated_conjecture, (r2_hidden(esk12_0,k9_relat_1(esk11_0,esk9_0))|~v1_xboole_0(k2_zfmisc_1(esk10_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_16])])).
% 43.90/44.08  cnf(c_0_44, negated_conjecture, (~m1_subset_1(esk7_3(esk12_0,X1,esk11_0),esk10_0)|~r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))|~r2_hidden(esk7_3(esk12_0,X1,esk11_0),esk9_0)|~r2_hidden(esk12_0,k9_relat_1(esk11_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_24])])).
% 43.90/44.08  cnf(c_0_45, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 43.90/44.08  cnf(c_0_46, negated_conjecture, (r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))|r2_hidden(esk12_0,k9_relat_1(esk11_0,esk9_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 43.90/44.08  fof(c_0_47, plain, ![X7, X8, X9, X10]:(((r2_hidden(X7,X9)|~r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)))&(r2_hidden(X8,X10)|~r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10))))&(~r2_hidden(X7,X9)|~r2_hidden(X8,X10)|r2_hidden(k4_tarski(X7,X8),k2_zfmisc_1(X9,X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 43.90/44.08  cnf(c_0_48, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 43.90/44.08  cnf(c_0_49, negated_conjecture, (m1_subset_1(k4_tarski(esk7_3(X1,X2,esk11_0),X1),k2_zfmisc_1(esk10_0,esk8_0))|~r2_hidden(X1,k9_relat_1(esk11_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_36]), c_0_24])])).
% 43.90/44.08  cnf(c_0_50, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk10_0,esk8_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 43.90/44.08  cnf(c_0_51, negated_conjecture, (~r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))|~r2_hidden(esk7_3(esk12_0,X1,esk11_0),esk9_0)|~r2_hidden(esk7_3(esk12_0,X1,esk11_0),esk10_0)|~r2_hidden(esk12_0,k9_relat_1(esk11_0,X1))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 43.90/44.08  cnf(c_0_52, plain, (r2_hidden(esk7_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 43.90/44.08  cnf(c_0_53, negated_conjecture, (r2_hidden(esk12_0,k9_relat_1(esk11_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_34]), c_0_16])])).
% 43.90/44.08  cnf(c_0_54, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 43.90/44.08  cnf(c_0_55, negated_conjecture, (r2_hidden(k4_tarski(esk7_3(X1,X2,esk11_0),X1),k2_zfmisc_1(esk10_0,esk8_0))|~r2_hidden(X1,k9_relat_1(esk11_0,X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 43.90/44.08  cnf(c_0_56, negated_conjecture, (~r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))|~r2_hidden(esk7_3(esk12_0,esk9_0,esk11_0),esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_24])])).
% 43.90/44.08  cnf(c_0_57, negated_conjecture, (r2_hidden(esk7_3(X1,X2,esk11_0),esk10_0)|~r2_hidden(X1,k9_relat_1(esk11_0,X2))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 43.90/44.08  cnf(c_0_58, negated_conjecture, (~r2_hidden(esk12_0,k7_relset_1(esk10_0,esk8_0,esk11_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_53])])).
% 43.90/44.08  cnf(c_0_59, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_34]), c_0_53]), c_0_16])]), ['proof']).
% 43.90/44.08  # SZS output end CNFRefutation
% 43.90/44.08  # Proof object total steps             : 60
% 43.90/44.08  # Proof object clause steps            : 37
% 43.90/44.08  # Proof object formula steps           : 23
% 43.90/44.08  # Proof object conjectures             : 28
% 43.90/44.08  # Proof object clause conjectures      : 25
% 43.90/44.08  # Proof object formula conjectures     : 3
% 43.90/44.08  # Proof object initial clauses used    : 16
% 43.90/44.08  # Proof object initial formulas used   : 11
% 43.90/44.08  # Proof object generating inferences   : 21
% 43.90/44.08  # Proof object simplifying inferences  : 21
% 43.90/44.08  # Training examples: 0 positive, 0 negative
% 43.90/44.08  # Parsed axioms                        : 11
% 43.90/44.08  # Removed by relevancy pruning/SinE    : 0
% 43.90/44.08  # Initial clauses                      : 32
% 43.90/44.08  # Removed in clause preprocessing      : 0
% 43.90/44.08  # Initial clauses in saturation        : 32
% 43.90/44.08  # Processed clauses                    : 30478
% 43.90/44.08  # ...of these trivial                  : 34
% 43.90/44.08  # ...subsumed                          : 16703
% 43.90/44.08  # ...remaining for further processing  : 13741
% 43.90/44.08  # Other redundant clauses eliminated   : 345
% 43.90/44.08  # Clauses deleted for lack of memory   : 129450
% 43.90/44.08  # Backward-subsumed                    : 265
% 43.90/44.08  # Backward-rewritten                   : 31
% 43.90/44.08  # Generated clauses                    : 4488329
% 43.90/44.08  # ...of the previous two non-trivial   : 4481592
% 43.90/44.08  # Contextual simplify-reflections      : 66
% 43.90/44.08  # Paramodulations                      : 4483739
% 43.90/44.08  # Factorizations                       : 24
% 43.90/44.08  # Equation resolutions                 : 1588
% 43.90/44.08  # Propositional unsat checks           : 0
% 43.90/44.08  #    Propositional check models        : 0
% 43.90/44.08  #    Propositional check unsatisfiable : 0
% 43.90/44.08  #    Propositional clauses             : 0
% 43.90/44.08  #    Propositional clauses after purity: 0
% 43.90/44.08  #    Propositional unsat core size     : 0
% 43.90/44.08  #    Propositional preprocessing time  : 0.000
% 43.90/44.08  #    Propositional encoding time       : 0.000
% 43.90/44.08  #    Propositional solver time         : 0.000
% 43.90/44.08  #    Success case prop preproc time    : 0.000
% 43.90/44.08  #    Success case prop encoding time   : 0.000
% 43.90/44.08  #    Success case prop solver time     : 0.000
% 43.90/44.08  # Current number of processed clauses  : 10435
% 43.90/44.08  #    Positive orientable unit clauses  : 10
% 43.90/44.08  #    Positive unorientable unit clauses: 0
% 43.90/44.08  #    Negative unit clauses             : 6
% 43.90/44.08  #    Non-unit-clauses                  : 10419
% 43.90/44.08  # Current number of unprocessed clauses: 2189556
% 43.90/44.08  # ...number of literals in the above   : 8658481
% 43.90/44.08  # Current number of archived formulas  : 0
% 43.90/44.08  # Current number of archived clauses   : 3306
% 43.90/44.08  # Clause-clause subsumption calls (NU) : 13950844
% 43.90/44.08  # Rec. Clause-clause subsumption calls : 7717597
% 43.90/44.08  # Non-unit clause-clause subsumptions  : 15488
% 43.90/44.08  # Unit Clause-clause subsumption calls : 9436
% 43.90/44.08  # Rewrite failures with RHS unbound    : 0
% 43.90/44.08  # BW rewrite match attempts            : 1505
% 43.90/44.08  # BW rewrite match successes           : 6
% 43.90/44.08  # Condensation attempts                : 0
% 43.90/44.08  # Condensation successes               : 0
% 43.90/44.08  # Termbank termtop insertions          : 109262089
% 43.95/44.16  
% 43.95/44.16  # -------------------------------------------------
% 43.95/44.16  # User time                : 42.786 s
% 43.95/44.16  # System time              : 1.018 s
% 43.95/44.16  # Total time               : 43.805 s
% 43.95/44.16  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
