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
% DateTime   : Thu Dec  3 10:58:43 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 182 expanded)
%              Number of clauses        :   32 (  71 expanded)
%              Number of leaves         :   10 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  196 (1052 expanded)
%              Number of equality atoms :   12 (  27 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | v1_relat_1(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_12,negated_conjecture,(
    ! [X47] :
      ( ~ v1_xboole_0(esk5_0)
      & ~ v1_xboole_0(esk6_0)
      & ~ v1_xboole_0(esk7_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0)))
      & m1_subset_1(esk9_0,esk5_0)
      & ( ~ r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0))
        | ~ m1_subset_1(X47,esk7_0)
        | ~ r2_hidden(k4_tarski(X47,esk9_0),esk8_0)
        | ~ r2_hidden(X47,esk6_0) )
      & ( m1_subset_1(esk10_0,esk7_0)
        | r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0)) )
      & ( r2_hidden(k4_tarski(esk10_0,esk9_0),esk8_0)
        | r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0)) )
      & ( r2_hidden(esk10_0,esk6_0)
        | r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).

fof(c_0_13,plain,(
    ! [X28,X29] : v1_relat_1(k2_zfmisc_1(X28,X29)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_14,plain,(
    ! [X14,X15,X16,X17,X19,X20,X21,X22,X24] :
      ( ( r2_hidden(k4_tarski(esk1_4(X14,X15,X16,X17),X17),X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k9_relat_1(X14,X15)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk1_4(X14,X15,X16,X17),X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k9_relat_1(X14,X15)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(X20,X19),X14)
        | ~ r2_hidden(X20,X15)
        | r2_hidden(X19,X16)
        | X16 != k9_relat_1(X14,X15)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(esk2_3(X14,X21,X22),X22)
        | ~ r2_hidden(k4_tarski(X24,esk2_3(X14,X21,X22)),X14)
        | ~ r2_hidden(X24,X21)
        | X22 = k9_relat_1(X14,X21)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk3_3(X14,X21,X22),esk2_3(X14,X21,X22)),X14)
        | r2_hidden(esk2_3(X14,X21,X22),X22)
        | X22 = k9_relat_1(X14,X21)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk3_3(X14,X21,X22),X21)
        | r2_hidden(esk2_3(X14,X21,X22),X22)
        | X22 = k9_relat_1(X14,X21)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

cnf(c_0_15,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X35,X36,X37] :
      ( ( v4_relat_1(X37,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( v5_relat_1(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X2,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X5 != k9_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk9_0),esk8_0)
    | r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

fof(c_0_22,plain,(
    ! [X26,X27] :
      ( ( ~ v4_relat_1(X27,X26)
        | r1_tarski(k1_relat_1(X27),X26)
        | ~ v1_relat_1(X27) )
      & ( ~ r1_tarski(k1_relat_1(X27),X26)
        | v4_relat_1(X27,X26)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_23,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0))
    | r2_hidden(esk9_0,X1)
    | X1 != k9_relat_1(esk8_0,X2)
    | ~ r2_hidden(esk10_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

fof(c_0_25,plain,(
    ! [X38,X39,X40,X41] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | k7_relset_1(X38,X39,X40,X41) = k9_relat_1(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_26,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_27,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( v4_relat_1(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0))
    | r2_hidden(esk9_0,k9_relat_1(esk8_0,X1))
    | ~ r2_hidden(esk10_0,X1) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk10_0,esk6_0)
    | r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0))
    | ~ m1_subset_1(X1,esk7_0)
    | ~ r2_hidden(k4_tarski(X1,esk9_0),esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X9,X10,X11] :
      ( ~ r2_hidden(X9,X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X11))
      | m1_subset_1(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_21])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0))
    | r2_hidden(esk9_0,k9_relat_1(esk8_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k9_relat_1(esk8_0,esk6_0))
    | ~ r2_hidden(k4_tarski(X1,esk9_0),esk8_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_16])])).

fof(c_0_38,plain,(
    ! [X30,X31,X32,X34] :
      ( ( r2_hidden(esk4_3(X30,X31,X32),k1_relat_1(X32))
        | ~ r2_hidden(X30,k9_relat_1(X32,X31))
        | ~ v1_relat_1(X32) )
      & ( r2_hidden(k4_tarski(esk4_3(X30,X31,X32),X30),X32)
        | ~ r2_hidden(X30,k9_relat_1(X32,X31))
        | ~ v1_relat_1(X32) )
      & ( r2_hidden(esk4_3(X30,X31,X32),X31)
        | ~ r2_hidden(X30,k9_relat_1(X32,X31))
        | ~ v1_relat_1(X32) )
      & ( ~ r2_hidden(X34,k1_relat_1(X32))
        | ~ r2_hidden(k4_tarski(X34,X30),X32)
        | ~ r2_hidden(X34,X31)
        | r2_hidden(X30,k9_relat_1(X32,X31))
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk8_0),k1_zfmisc_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk9_0),esk8_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_36]),c_0_37])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(X1,esk7_0)
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk10_0,esk7_0)
    | r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)
    | ~ r2_hidden(esk9_0,k9_relat_1(esk8_0,X1))
    | ~ m1_subset_1(esk4_3(esk9_0,X1,esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_21])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk4_3(X1,X2,esk8_0),esk7_0)
    | ~ r2_hidden(X1,k9_relat_1(esk8_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_21])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_20]),c_0_45]),c_0_30])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)
    | ~ r2_hidden(esk9_0,k9_relat_1(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk9_0,k9_relat_1(esk8_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_32]),c_0_16])])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:16:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t52_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 0.14/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.14/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.14/0.38  fof(d13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X5,X4),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 0.14/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.14/0.38  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.14/0.38  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.14/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.14/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.14/0.38  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.14/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2))))))))), inference(assume_negation,[status(cth)],[t52_relset_1])).
% 0.14/0.38  fof(c_0_11, plain, ![X12, X13]:(~v1_relat_1(X12)|(~m1_subset_1(X13,k1_zfmisc_1(X12))|v1_relat_1(X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.14/0.38  fof(c_0_12, negated_conjecture, ![X47]:(~v1_xboole_0(esk5_0)&(~v1_xboole_0(esk6_0)&(~v1_xboole_0(esk7_0)&(m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0)))&(m1_subset_1(esk9_0,esk5_0)&((~r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0))|(~m1_subset_1(X47,esk7_0)|~r2_hidden(k4_tarski(X47,esk9_0),esk8_0)|~r2_hidden(X47,esk6_0)))&(((m1_subset_1(esk10_0,esk7_0)|r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0)))&(r2_hidden(k4_tarski(esk10_0,esk9_0),esk8_0)|r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0))))&(r2_hidden(esk10_0,esk6_0)|r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0)))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).
% 0.14/0.38  fof(c_0_13, plain, ![X28, X29]:v1_relat_1(k2_zfmisc_1(X28,X29)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.14/0.38  fof(c_0_14, plain, ![X14, X15, X16, X17, X19, X20, X21, X22, X24]:((((r2_hidden(k4_tarski(esk1_4(X14,X15,X16,X17),X17),X14)|~r2_hidden(X17,X16)|X16!=k9_relat_1(X14,X15)|~v1_relat_1(X14))&(r2_hidden(esk1_4(X14,X15,X16,X17),X15)|~r2_hidden(X17,X16)|X16!=k9_relat_1(X14,X15)|~v1_relat_1(X14)))&(~r2_hidden(k4_tarski(X20,X19),X14)|~r2_hidden(X20,X15)|r2_hidden(X19,X16)|X16!=k9_relat_1(X14,X15)|~v1_relat_1(X14)))&((~r2_hidden(esk2_3(X14,X21,X22),X22)|(~r2_hidden(k4_tarski(X24,esk2_3(X14,X21,X22)),X14)|~r2_hidden(X24,X21))|X22=k9_relat_1(X14,X21)|~v1_relat_1(X14))&((r2_hidden(k4_tarski(esk3_3(X14,X21,X22),esk2_3(X14,X21,X22)),X14)|r2_hidden(esk2_3(X14,X21,X22),X22)|X22=k9_relat_1(X14,X21)|~v1_relat_1(X14))&(r2_hidden(esk3_3(X14,X21,X22),X21)|r2_hidden(esk2_3(X14,X21,X22),X22)|X22=k9_relat_1(X14,X21)|~v1_relat_1(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).
% 0.14/0.38  cnf(c_0_15, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_17, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  fof(c_0_18, plain, ![X35, X36, X37]:((v4_relat_1(X37,X35)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(v5_relat_1(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.14/0.38  cnf(c_0_19, plain, (r2_hidden(X2,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X5!=k9_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk9_0),esk8_0)|r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.14/0.38  fof(c_0_22, plain, ![X26, X27]:((~v4_relat_1(X27,X26)|r1_tarski(k1_relat_1(X27),X26)|~v1_relat_1(X27))&(~r1_tarski(k1_relat_1(X27),X26)|v4_relat_1(X27,X26)|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.14/0.38  cnf(c_0_23, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0))|r2_hidden(esk9_0,X1)|X1!=k9_relat_1(esk8_0,X2)|~r2_hidden(esk10_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.14/0.38  fof(c_0_25, plain, ![X38, X39, X40, X41]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|k7_relset_1(X38,X39,X40,X41)=k9_relat_1(X40,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.14/0.38  fof(c_0_26, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.14/0.38  cnf(c_0_27, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (v4_relat_1(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_23, c_0_16])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0))|r2_hidden(esk9_0,k9_relat_1(esk8_0,X1))|~r2_hidden(esk10_0,X1)), inference(er,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(esk10_0,esk6_0)|r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (~r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0))|~m1_subset_1(X1,esk7_0)|~r2_hidden(k4_tarski(X1,esk9_0),esk8_0)|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_32, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.38  fof(c_0_33, plain, ![X9, X10, X11]:(~r2_hidden(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X11))|m1_subset_1(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.14/0.38  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (r1_tarski(k1_relat_1(esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_21])])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0))|r2_hidden(esk9_0,k9_relat_1(esk8_0,esk6_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (~r2_hidden(esk9_0,k9_relat_1(esk8_0,esk6_0))|~r2_hidden(k4_tarski(X1,esk9_0),esk8_0)|~r2_hidden(X1,esk6_0)|~m1_subset_1(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_16])])).
% 0.14/0.38  fof(c_0_38, plain, ![X30, X31, X32, X34]:((((r2_hidden(esk4_3(X30,X31,X32),k1_relat_1(X32))|~r2_hidden(X30,k9_relat_1(X32,X31))|~v1_relat_1(X32))&(r2_hidden(k4_tarski(esk4_3(X30,X31,X32),X30),X32)|~r2_hidden(X30,k9_relat_1(X32,X31))|~v1_relat_1(X32)))&(r2_hidden(esk4_3(X30,X31,X32),X31)|~r2_hidden(X30,k9_relat_1(X32,X31))|~v1_relat_1(X32)))&(~r2_hidden(X34,k1_relat_1(X32))|~r2_hidden(k4_tarski(X34,X30),X32)|~r2_hidden(X34,X31)|r2_hidden(X30,k9_relat_1(X32,X31))|~v1_relat_1(X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.14/0.38  cnf(c_0_39, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (m1_subset_1(k1_relat_1(esk8_0),k1_zfmisc_1(esk7_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk9_0),esk8_0)|~r2_hidden(X1,esk6_0)|~m1_subset_1(X1,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_36]), c_0_37])).
% 0.14/0.38  cnf(c_0_42, plain, (r2_hidden(k4_tarski(esk4_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (m1_subset_1(X1,esk7_0)|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.14/0.38  cnf(c_0_44, plain, (r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk10_0,esk7_0)|r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (~r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)|~r2_hidden(esk9_0,k9_relat_1(esk8_0,X1))|~m1_subset_1(esk4_3(esk9_0,X1,esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_21])])).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk4_3(X1,X2,esk8_0),esk7_0)|~r2_hidden(X1,k9_relat_1(esk8_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_21])])).
% 0.14/0.38  cnf(c_0_48, negated_conjecture, (r2_hidden(esk9_0,k7_relset_1(esk7_0,esk5_0,esk8_0,esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_20]), c_0_45]), c_0_30])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (~r2_hidden(esk4_3(esk9_0,X1,esk8_0),esk6_0)|~r2_hidden(esk9_0,k9_relat_1(esk8_0,X1))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.14/0.38  cnf(c_0_50, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, (r2_hidden(esk9_0,k9_relat_1(esk8_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_32]), c_0_16])])).
% 0.14/0.38  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_21])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 53
% 0.14/0.38  # Proof object clause steps            : 32
% 0.14/0.38  # Proof object formula steps           : 21
% 0.14/0.38  # Proof object conjectures             : 24
% 0.14/0.38  # Proof object clause conjectures      : 21
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 16
% 0.14/0.38  # Proof object initial formulas used   : 10
% 0.14/0.38  # Proof object generating inferences   : 16
% 0.14/0.38  # Proof object simplifying inferences  : 20
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 10
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 29
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 29
% 0.14/0.38  # Processed clauses                    : 80
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 80
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 5
% 0.14/0.38  # Backward-rewritten                   : 6
% 0.14/0.38  # Generated clauses                    : 48
% 0.14/0.38  # ...of the previous two non-trivial   : 44
% 0.14/0.38  # Contextual simplify-reflections      : 3
% 0.14/0.38  # Paramodulations                      : 47
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 1
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
% 0.14/0.38  # Current number of processed clauses  : 40
% 0.14/0.38  #    Positive orientable unit clauses  : 10
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 3
% 0.14/0.38  #    Non-unit-clauses                  : 27
% 0.14/0.38  # Current number of unprocessed clauses: 21
% 0.14/0.38  # ...number of literals in the above   : 89
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 40
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 203
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 81
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 7
% 0.14/0.38  # Unit Clause-clause subsumption calls : 17
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 3352
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.030 s
% 0.14/0.38  # System time              : 0.006 s
% 0.14/0.38  # Total time               : 0.036 s
% 0.14/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
