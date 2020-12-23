%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:30 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   71 (5025 expanded)
%              Number of clauses        :   53 (1899 expanded)
%              Number of leaves         :    9 (1189 expanded)
%              Depth                    :   18
%              Number of atoms          :  270 (27911 expanded)
%              Number of equality atoms :   94 (7878 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(t16_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] :
                  ~ ( r2_hidden(X5,X1)
                    & X4 = k1_funct_1(X3,X5) ) )
       => k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(t23_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X5,X4),X3) )
      <=> k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_9,plain,(
    ! [X11,X12,X13,X14,X16,X17,X18,X19,X21] :
      ( ( r2_hidden(esk2_4(X11,X12,X13,X14),k1_relat_1(X11))
        | ~ r2_hidden(X14,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk2_4(X11,X12,X13,X14),X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( X14 = k1_funct_1(X11,esk2_4(X11,X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(X17,k1_relat_1(X11))
        | ~ r2_hidden(X17,X12)
        | X16 != k1_funct_1(X11,X17)
        | r2_hidden(X16,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(esk3_3(X11,X18,X19),X19)
        | ~ r2_hidden(X21,k1_relat_1(X11))
        | ~ r2_hidden(X21,X18)
        | esk3_3(X11,X18,X19) != k1_funct_1(X11,X21)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk4_3(X11,X18,X19),k1_relat_1(X11))
        | r2_hidden(esk3_3(X11,X18,X19),X19)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk4_3(X11,X18,X19),X18)
        | r2_hidden(esk3_3(X11,X18,X19),X19)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk3_3(X11,X18,X19) = k1_funct_1(X11,esk4_3(X11,X18,X19))
        | r2_hidden(esk3_3(X11,X18,X19),X19)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ! [X4] :
              ~ ( r2_hidden(X4,X2)
                & ! [X5] :
                    ~ ( r2_hidden(X5,X1)
                      & X4 = k1_funct_1(X3,X5) ) )
         => k2_relset_1(X1,X2,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t16_funct_2])).

cnf(c_0_11,plain,
    ( r2_hidden(X4,X5)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X4 != k1_funct_1(X2,X1)
    | X5 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,negated_conjecture,(
    ! [X45] :
      ( v1_funct_1(esk9_0)
      & v1_funct_2(esk9_0,esk7_0,esk8_0)
      & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))
      & ( r2_hidden(esk10_1(X45),esk7_0)
        | ~ r2_hidden(X45,esk8_0) )
      & ( X45 = k1_funct_1(esk9_0,esk10_1(X45))
        | ~ r2_hidden(X45,esk8_0) )
      & k2_relset_1(esk7_0,esk8_0,esk9_0) != esk8_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).

fof(c_0_13,plain,(
    ! [X32,X33,X34,X36,X37] :
      ( ( r2_hidden(esk5_3(X32,X33,X34),X33)
        | k2_relset_1(X32,X33,X34) = X33
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( ~ r2_hidden(k4_tarski(X36,esk5_3(X32,X33,X34)),X34)
        | k2_relset_1(X32,X33,X34) = X33
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( k2_relset_1(X32,X33,X34) != X33
        | ~ r2_hidden(X37,X33)
        | r2_hidden(k4_tarski(esk6_4(X32,X33,X34,X37),X37),X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_relset_1])])])])])])).

fof(c_0_14,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k1_relset_1(X26,X27,X28) = k1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_15,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X2,X3)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_11])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk10_1(X1),esk7_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | k2_relset_1(X1,X2,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( k2_relset_1(esk7_0,esk8_0,esk9_0) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X39,X40,X41] :
      ( ( ~ v1_funct_2(X41,X39,X40)
        | X39 = k1_relset_1(X39,X40,X41)
        | X40 = k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X39 != k1_relset_1(X39,X40,X41)
        | v1_funct_2(X41,X39,X40)
        | X40 = k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( ~ v1_funct_2(X41,X39,X40)
        | X39 = k1_relset_1(X39,X40,X41)
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X39 != k1_relset_1(X39,X40,X41)
        | v1_funct_2(X41,X39,X40)
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( ~ v1_funct_2(X41,X39,X40)
        | X41 = k1_xboole_0
        | X39 = k1_xboole_0
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X41 != k1_xboole_0
        | v1_funct_2(X41,X39,X40)
        | X39 = k1_xboole_0
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_21,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | v1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k1_funct_1(X1,esk10_1(X2)),k9_relat_1(X1,esk7_0))
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(esk10_1(X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,esk8_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk5_3(esk7_0,esk8_0,esk9_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_25,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( k1_relset_1(esk7_0,esk8_0,esk9_0) = k1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k1_funct_1(esk9_0,esk10_1(X1))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k1_funct_1(X1,esk10_1(esk5_3(esk7_0,esk8_0,esk9_0))),k9_relat_1(X1,esk7_0))
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(esk10_1(esk5_3(esk7_0,esk8_0,esk9_0)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk7_0
    | esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_18])])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(esk9_0,esk10_1(esk5_3(esk7_0,esk8_0,esk9_0))) = esk5_3(esk7_0,esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_18])).

fof(c_0_35,plain,(
    ! [X6,X7,X8,X10] :
      ( ( r2_hidden(esk1_3(X6,X7,X8),k1_relat_1(X8))
        | ~ r2_hidden(X6,k9_relat_1(X8,X7))
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(k4_tarski(esk1_3(X6,X7,X8),X6),X8)
        | ~ r2_hidden(X6,k9_relat_1(X8,X7))
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk1_3(X6,X7,X8),X7)
        | ~ r2_hidden(X6,k9_relat_1(X8,X7))
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(X10,k1_relat_1(X8))
        | ~ r2_hidden(k4_tarski(X10,X6),X8)
        | ~ r2_hidden(X10,X7)
        | r2_hidden(X6,k9_relat_1(X8,X7))
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_36,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(esk5_3(esk7_0,esk8_0,esk9_0),k9_relat_1(esk9_0,esk7_0))
    | ~ r2_hidden(esk10_1(esk5_3(esk7_0,esk8_0,esk9_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_37,plain,
    ( k2_relset_1(X2,X3,X4) = X3
    | ~ r2_hidden(k4_tarski(X1,esk5_3(X2,X3,X4)),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(esk5_3(esk7_0,esk8_0,esk9_0),k9_relat_1(esk9_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_16]),c_0_24])])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk5_3(esk7_0,esk8_0,esk9_0)),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_18]),c_0_19])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_34])]),c_0_40])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_42])).

cnf(c_0_46,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_48,negated_conjecture,
    ( k1_relset_1(esk7_0,k1_xboole_0,esk9_0) = k1_relat_1(esk9_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_42])).

cnf(c_0_49,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | v1_funct_2(esk9_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk9_0) = k1_relat_1(esk9_0)
    | esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk9_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k1_funct_1(X1,esk10_1(esk5_3(esk7_0,k1_xboole_0,esk9_0))),k9_relat_1(X1,esk7_0))
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(esk10_1(esk5_3(esk7_0,k1_xboole_0,esk9_0)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_42]),c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( k1_relat_1(esk9_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( k1_funct_1(esk9_0,esk10_1(esk5_3(esk7_0,k1_xboole_0,esk9_0))) = esk5_3(esk7_0,k1_xboole_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_42]),c_0_42])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk10_1(X1),esk7_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_42])).

cnf(c_0_58,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r2_hidden(esk5_3(esk7_0,k1_xboole_0,esk9_0),k9_relat_1(esk9_0,esk7_0))
    | ~ r2_hidden(esk10_1(esk5_3(esk7_0,k1_xboole_0,esk9_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_33]),c_0_34])])).

cnf(c_0_59,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r2_hidden(esk10_1(X1),k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_47])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk5_3(esk7_0,k1_xboole_0,esk9_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_42]),c_0_42])).

cnf(c_0_61,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | r2_hidden(esk5_3(esk7_0,k1_xboole_0,esk9_0),k9_relat_1(esk9_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk5_3(esk7_0,k1_xboole_0,esk9_0)),esk9_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_42])).

fof(c_0_63,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k2_relset_1(X29,X30,X31) = k2_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_64,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_61]),c_0_34])]),c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( k2_relset_1(esk7_0,k1_xboole_0,esk9_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_42]),c_0_42])).

cnf(c_0_66,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_64])).

cnf(c_0_68,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_69,negated_conjecture,
    ( k2_relset_1(esk7_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_65,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:27:40 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.15/0.40  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.15/0.40  #
% 0.15/0.40  # Preprocessing time       : 0.028 s
% 0.15/0.40  # Presaturation interreduction done
% 0.15/0.40  
% 0.15/0.40  # Proof found!
% 0.15/0.40  # SZS status Theorem
% 0.15/0.40  # SZS output start CNFRefutation
% 0.15/0.40  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 0.15/0.40  fof(t16_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 0.15/0.40  fof(t23_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X5,X4),X3))))<=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 0.15/0.40  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.15/0.40  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.15/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.15/0.40  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.15/0.40  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.15/0.40  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.15/0.40  fof(c_0_9, plain, ![X11, X12, X13, X14, X16, X17, X18, X19, X21]:(((((r2_hidden(esk2_4(X11,X12,X13,X14),k1_relat_1(X11))|~r2_hidden(X14,X13)|X13!=k9_relat_1(X11,X12)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(r2_hidden(esk2_4(X11,X12,X13,X14),X12)|~r2_hidden(X14,X13)|X13!=k9_relat_1(X11,X12)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&(X14=k1_funct_1(X11,esk2_4(X11,X12,X13,X14))|~r2_hidden(X14,X13)|X13!=k9_relat_1(X11,X12)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&(~r2_hidden(X17,k1_relat_1(X11))|~r2_hidden(X17,X12)|X16!=k1_funct_1(X11,X17)|r2_hidden(X16,X13)|X13!=k9_relat_1(X11,X12)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&((~r2_hidden(esk3_3(X11,X18,X19),X19)|(~r2_hidden(X21,k1_relat_1(X11))|~r2_hidden(X21,X18)|esk3_3(X11,X18,X19)!=k1_funct_1(X11,X21))|X19=k9_relat_1(X11,X18)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(((r2_hidden(esk4_3(X11,X18,X19),k1_relat_1(X11))|r2_hidden(esk3_3(X11,X18,X19),X19)|X19=k9_relat_1(X11,X18)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(r2_hidden(esk4_3(X11,X18,X19),X18)|r2_hidden(esk3_3(X11,X18,X19),X19)|X19=k9_relat_1(X11,X18)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&(esk3_3(X11,X18,X19)=k1_funct_1(X11,esk4_3(X11,X18,X19))|r2_hidden(esk3_3(X11,X18,X19),X19)|X19=k9_relat_1(X11,X18)|(~v1_relat_1(X11)|~v1_funct_1(X11)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 0.15/0.40  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2))), inference(assume_negation,[status(cth)],[t16_funct_2])).
% 0.15/0.40  cnf(c_0_11, plain, (r2_hidden(X4,X5)|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,X3)|X4!=k1_funct_1(X2,X1)|X5!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.40  fof(c_0_12, negated_conjecture, ![X45]:(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk7_0,esk8_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))))&(((r2_hidden(esk10_1(X45),esk7_0)|~r2_hidden(X45,esk8_0))&(X45=k1_funct_1(esk9_0,esk10_1(X45))|~r2_hidden(X45,esk8_0)))&k2_relset_1(esk7_0,esk8_0,esk9_0)!=esk8_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).
% 0.15/0.40  fof(c_0_13, plain, ![X32, X33, X34, X36, X37]:(((r2_hidden(esk5_3(X32,X33,X34),X33)|k2_relset_1(X32,X33,X34)=X33|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(~r2_hidden(k4_tarski(X36,esk5_3(X32,X33,X34)),X34)|k2_relset_1(X32,X33,X34)=X33|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&(k2_relset_1(X32,X33,X34)!=X33|(~r2_hidden(X37,X33)|r2_hidden(k4_tarski(esk6_4(X32,X33,X34,X37),X37),X34))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_relset_1])])])])])])).
% 0.15/0.40  fof(c_0_14, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k1_relset_1(X26,X27,X28)=k1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.15/0.40  cnf(c_0_15, plain, (r2_hidden(k1_funct_1(X1,X2),k9_relat_1(X1,X3))|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X2,X3)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_11])])).
% 0.15/0.40  cnf(c_0_16, negated_conjecture, (r2_hidden(esk10_1(X1),esk7_0)|~r2_hidden(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.40  cnf(c_0_17, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|k2_relset_1(X1,X2,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.40  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.40  cnf(c_0_19, negated_conjecture, (k2_relset_1(esk7_0,esk8_0,esk9_0)!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.40  fof(c_0_20, plain, ![X39, X40, X41]:((((~v1_funct_2(X41,X39,X40)|X39=k1_relset_1(X39,X40,X41)|X40=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(X39!=k1_relset_1(X39,X40,X41)|v1_funct_2(X41,X39,X40)|X40=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))&((~v1_funct_2(X41,X39,X40)|X39=k1_relset_1(X39,X40,X41)|X39!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(X39!=k1_relset_1(X39,X40,X41)|v1_funct_2(X41,X39,X40)|X39!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))))&((~v1_funct_2(X41,X39,X40)|X41=k1_xboole_0|X39=k1_xboole_0|X40!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(X41!=k1_xboole_0|v1_funct_2(X41,X39,X40)|X39=k1_xboole_0|X40!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.15/0.40  cnf(c_0_21, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.40  fof(c_0_22, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|v1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.15/0.40  cnf(c_0_23, negated_conjecture, (r2_hidden(k1_funct_1(X1,esk10_1(X2)),k9_relat_1(X1,esk7_0))|~v1_funct_1(X1)|~r2_hidden(esk10_1(X2),k1_relat_1(X1))|~r2_hidden(X2,esk8_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.15/0.40  cnf(c_0_24, negated_conjecture, (r2_hidden(esk5_3(esk7_0,esk8_0,esk9_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.15/0.40  cnf(c_0_25, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.40  cnf(c_0_26, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.40  cnf(c_0_27, negated_conjecture, (k1_relset_1(esk7_0,esk8_0,esk9_0)=k1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 0.15/0.40  cnf(c_0_28, negated_conjecture, (X1=k1_funct_1(esk9_0,esk10_1(X1))|~r2_hidden(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.40  cnf(c_0_29, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.15/0.40  cnf(c_0_30, negated_conjecture, (r2_hidden(k1_funct_1(X1,esk10_1(esk5_3(esk7_0,esk8_0,esk9_0))),k9_relat_1(X1,esk7_0))|~v1_funct_1(X1)|~r2_hidden(esk10_1(esk5_3(esk7_0,esk8_0,esk9_0)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.15/0.40  cnf(c_0_31, negated_conjecture, (k1_relat_1(esk9_0)=esk7_0|esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_18])])).
% 0.15/0.40  cnf(c_0_32, negated_conjecture, (k1_funct_1(esk9_0,esk10_1(esk5_3(esk7_0,esk8_0,esk9_0)))=esk5_3(esk7_0,esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_28, c_0_24])).
% 0.15/0.40  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.40  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_29, c_0_18])).
% 0.15/0.40  fof(c_0_35, plain, ![X6, X7, X8, X10]:((((r2_hidden(esk1_3(X6,X7,X8),k1_relat_1(X8))|~r2_hidden(X6,k9_relat_1(X8,X7))|~v1_relat_1(X8))&(r2_hidden(k4_tarski(esk1_3(X6,X7,X8),X6),X8)|~r2_hidden(X6,k9_relat_1(X8,X7))|~v1_relat_1(X8)))&(r2_hidden(esk1_3(X6,X7,X8),X7)|~r2_hidden(X6,k9_relat_1(X8,X7))|~v1_relat_1(X8)))&(~r2_hidden(X10,k1_relat_1(X8))|~r2_hidden(k4_tarski(X10,X6),X8)|~r2_hidden(X10,X7)|r2_hidden(X6,k9_relat_1(X8,X7))|~v1_relat_1(X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.15/0.40  cnf(c_0_36, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(esk5_3(esk7_0,esk8_0,esk9_0),k9_relat_1(esk9_0,esk7_0))|~r2_hidden(esk10_1(esk5_3(esk7_0,esk8_0,esk9_0)),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34])])).
% 0.15/0.40  cnf(c_0_37, plain, (k2_relset_1(X2,X3,X4)=X3|~r2_hidden(k4_tarski(X1,esk5_3(X2,X3,X4)),X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.40  cnf(c_0_38, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.15/0.40  cnf(c_0_39, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(esk5_3(esk7_0,esk8_0,esk9_0),k9_relat_1(esk9_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_16]), c_0_24])])).
% 0.15/0.40  cnf(c_0_40, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk5_3(esk7_0,esk8_0,esk9_0)),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_18]), c_0_19])).
% 0.15/0.40  cnf(c_0_41, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.40  cnf(c_0_42, negated_conjecture, (esk8_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_34])]), c_0_40])).
% 0.15/0.40  cnf(c_0_43, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_41])).
% 0.15/0.40  cnf(c_0_44, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_26, c_0_42])).
% 0.15/0.40  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_18, c_0_42])).
% 0.15/0.40  cnf(c_0_46, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.40  cnf(c_0_47, negated_conjecture, (esk7_0=k1_xboole_0|esk9_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.15/0.40  cnf(c_0_48, negated_conjecture, (k1_relset_1(esk7_0,k1_xboole_0,esk9_0)=k1_relat_1(esk9_0)), inference(rw,[status(thm)],[c_0_27, c_0_42])).
% 0.15/0.40  cnf(c_0_49, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_46])).
% 0.15/0.40  cnf(c_0_50, negated_conjecture, (esk9_0=k1_xboole_0|v1_funct_2(esk9_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_47])).
% 0.15/0.40  cnf(c_0_51, negated_conjecture, (esk9_0=k1_xboole_0|m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_45, c_0_47])).
% 0.15/0.40  cnf(c_0_52, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk9_0)=k1_relat_1(esk9_0)|esk9_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_47])).
% 0.15/0.40  cnf(c_0_53, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk9_0)=k1_xboole_0|esk9_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.15/0.40  cnf(c_0_54, negated_conjecture, (r2_hidden(k1_funct_1(X1,esk10_1(esk5_3(esk7_0,k1_xboole_0,esk9_0))),k9_relat_1(X1,esk7_0))|~v1_funct_1(X1)|~r2_hidden(esk10_1(esk5_3(esk7_0,k1_xboole_0,esk9_0)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_42]), c_0_42])).
% 0.15/0.40  cnf(c_0_55, negated_conjecture, (k1_relat_1(esk9_0)=k1_xboole_0|esk9_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.15/0.40  cnf(c_0_56, negated_conjecture, (k1_funct_1(esk9_0,esk10_1(esk5_3(esk7_0,k1_xboole_0,esk9_0)))=esk5_3(esk7_0,k1_xboole_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_42]), c_0_42])).
% 0.15/0.40  cnf(c_0_57, negated_conjecture, (r2_hidden(esk10_1(X1),esk7_0)|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_16, c_0_42])).
% 0.15/0.40  cnf(c_0_58, negated_conjecture, (esk9_0=k1_xboole_0|r2_hidden(esk5_3(esk7_0,k1_xboole_0,esk9_0),k9_relat_1(esk9_0,esk7_0))|~r2_hidden(esk10_1(esk5_3(esk7_0,k1_xboole_0,esk9_0)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_33]), c_0_34])])).
% 0.15/0.40  cnf(c_0_59, negated_conjecture, (esk9_0=k1_xboole_0|r2_hidden(esk10_1(X1),k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_47])).
% 0.15/0.40  cnf(c_0_60, negated_conjecture, (r2_hidden(esk5_3(esk7_0,k1_xboole_0,esk9_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_42]), c_0_42])).
% 0.15/0.40  cnf(c_0_61, negated_conjecture, (esk9_0=k1_xboole_0|r2_hidden(esk5_3(esk7_0,k1_xboole_0,esk9_0),k9_relat_1(esk9_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])])).
% 0.15/0.40  cnf(c_0_62, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk5_3(esk7_0,k1_xboole_0,esk9_0)),esk9_0)), inference(rw,[status(thm)],[c_0_40, c_0_42])).
% 0.15/0.40  fof(c_0_63, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k2_relset_1(X29,X30,X31)=k2_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.15/0.40  cnf(c_0_64, negated_conjecture, (esk9_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_61]), c_0_34])]), c_0_62])).
% 0.15/0.40  cnf(c_0_65, negated_conjecture, (k2_relset_1(esk7_0,k1_xboole_0,esk9_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_42]), c_0_42])).
% 0.15/0.40  cnf(c_0_66, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.15/0.40  cnf(c_0_67, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_45, c_0_64])).
% 0.15/0.40  cnf(c_0_68, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.15/0.40  cnf(c_0_69, negated_conjecture, (k2_relset_1(esk7_0,k1_xboole_0,k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_65, c_0_64])).
% 0.15/0.40  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_69]), ['proof']).
% 0.15/0.40  # SZS output end CNFRefutation
% 0.15/0.40  # Proof object total steps             : 71
% 0.15/0.40  # Proof object clause steps            : 53
% 0.15/0.40  # Proof object formula steps           : 18
% 0.15/0.40  # Proof object conjectures             : 42
% 0.15/0.40  # Proof object clause conjectures      : 39
% 0.15/0.40  # Proof object formula conjectures     : 3
% 0.15/0.40  # Proof object initial clauses used    : 17
% 0.15/0.40  # Proof object initial formulas used   : 9
% 0.15/0.40  # Proof object generating inferences   : 22
% 0.15/0.40  # Proof object simplifying inferences  : 47
% 0.15/0.40  # Training examples: 0 positive, 0 negative
% 0.15/0.40  # Parsed axioms                        : 9
% 0.15/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.40  # Initial clauses                      : 32
% 0.15/0.40  # Removed in clause preprocessing      : 0
% 0.15/0.40  # Initial clauses in saturation        : 32
% 0.15/0.40  # Processed clauses                    : 189
% 0.15/0.40  # ...of these trivial                  : 4
% 0.15/0.40  # ...subsumed                          : 13
% 0.15/0.40  # ...remaining for further processing  : 172
% 0.15/0.40  # Other redundant clauses eliminated   : 10
% 0.15/0.40  # Clauses deleted for lack of memory   : 0
% 0.15/0.40  # Backward-subsumed                    : 3
% 0.15/0.40  # Backward-rewritten                   : 92
% 0.15/0.40  # Generated clauses                    : 277
% 0.15/0.40  # ...of the previous two non-trivial   : 309
% 0.15/0.40  # Contextual simplify-reflections      : 1
% 0.15/0.40  # Paramodulations                      : 269
% 0.15/0.40  # Factorizations                       : 0
% 0.15/0.40  # Equation resolutions                 : 10
% 0.15/0.40  # Propositional unsat checks           : 0
% 0.15/0.40  #    Propositional check models        : 0
% 0.15/0.40  #    Propositional check unsatisfiable : 0
% 0.15/0.40  #    Propositional clauses             : 0
% 0.15/0.40  #    Propositional clauses after purity: 0
% 0.15/0.40  #    Propositional unsat core size     : 0
% 0.15/0.40  #    Propositional preprocessing time  : 0.000
% 0.15/0.40  #    Propositional encoding time       : 0.000
% 0.15/0.40  #    Propositional solver time         : 0.000
% 0.15/0.40  #    Success case prop preproc time    : 0.000
% 0.15/0.40  #    Success case prop encoding time   : 0.000
% 0.15/0.40  #    Success case prop solver time     : 0.000
% 0.15/0.40  # Current number of processed clauses  : 37
% 0.15/0.40  #    Positive orientable unit clauses  : 8
% 0.15/0.40  #    Positive unorientable unit clauses: 0
% 0.15/0.40  #    Negative unit clauses             : 2
% 0.15/0.40  #    Non-unit-clauses                  : 27
% 0.15/0.40  # Current number of unprocessed clauses: 162
% 0.15/0.40  # ...number of literals in the above   : 589
% 0.15/0.40  # Current number of archived formulas  : 0
% 0.15/0.40  # Current number of archived clauses   : 127
% 0.15/0.40  # Clause-clause subsumption calls (NU) : 959
% 0.15/0.40  # Rec. Clause-clause subsumption calls : 449
% 0.15/0.40  # Non-unit clause-clause subsumptions  : 16
% 0.15/0.40  # Unit Clause-clause subsumption calls : 12
% 0.15/0.40  # Rewrite failures with RHS unbound    : 0
% 0.15/0.40  # BW rewrite match attempts            : 4
% 0.15/0.40  # BW rewrite match successes           : 3
% 0.15/0.40  # Condensation attempts                : 0
% 0.15/0.40  # Condensation successes               : 0
% 0.15/0.40  # Termbank termtop insertions          : 11329
% 0.15/0.40  
% 0.15/0.40  # -------------------------------------------------
% 0.15/0.40  # User time                : 0.045 s
% 0.15/0.40  # System time              : 0.003 s
% 0.15/0.40  # Total time               : 0.048 s
% 0.15/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
