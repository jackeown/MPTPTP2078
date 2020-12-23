%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0837+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:16 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 195 expanded)
%              Number of clauses        :   42 (  91 expanded)
%              Number of leaves         :    9 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  145 ( 692 expanded)
%              Number of equality atoms :   11 (  62 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
             => ! [X4] :
                  ( r2_hidden(X4,k2_relset_1(X2,X1,X3))
                <=> ? [X5] :
                      ( m1_subset_1(X5,X2)
                      & r2_hidden(k4_tarski(X5,X4),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
               => ! [X4] :
                    ( r2_hidden(X4,k2_relset_1(X2,X1,X3))
                  <=> ? [X5] :
                        ( m1_subset_1(X5,X2)
                        & r2_hidden(k4_tarski(X5,X4),X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_relset_1])).

fof(c_0_10,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k2_relset_1(X19,X20,X21) = k2_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_11,negated_conjecture,(
    ! [X39] :
      ( ~ v1_xboole_0(esk5_0)
      & ~ v1_xboole_0(esk6_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))
      & ( ~ r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0))
        | ~ m1_subset_1(X39,esk6_0)
        | ~ r2_hidden(k4_tarski(X39,esk8_0),esk7_0) )
      & ( m1_subset_1(esk9_0,esk6_0)
        | r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0)) )
      & ( r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)
        | r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).

fof(c_0_12,plain,(
    ! [X6,X7,X8,X10,X11,X12,X13,X15] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),X8),X6)
        | X7 != k2_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(X11,X10),X6)
        | r2_hidden(X10,X7)
        | X7 != k2_relat_1(X6) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | ~ r2_hidden(k4_tarski(X15,esk2_2(X12,X13)),X12)
        | X13 = k2_relat_1(X12) )
      & ( r2_hidden(esk2_2(X12,X13),X13)
        | r2_hidden(k4_tarski(esk3_2(X12,X13),esk2_2(X12,X13)),X12)
        | X13 = k2_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_13,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X28,X29)
      | v1_xboole_0(X29)
      | r2_hidden(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_14,plain,(
    ! [X17] : m1_subset_1(esk4_1(X17),X17) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_15,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X33,X34] :
      ( ~ r2_hidden(X33,X34)
      | ~ v1_xboole_0(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk8_0),esk7_0)
    | r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( k2_relset_1(esk6_0,esk5_0,esk7_0) = k2_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X30,X31,X32] :
      ( ~ r2_hidden(X30,X31)
      | ~ m1_subset_1(X31,k1_zfmisc_1(X32))
      | m1_subset_1(X30,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk4_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk8_0,k2_relat_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_3(esk7_0,k2_relat_1(esk7_0),esk8_0),esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_33,plain,(
    ! [X22,X23,X24,X25] :
      ( ( r2_hidden(X22,X24)
        | ~ r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25)) )
      & ( r2_hidden(X23,X25)
        | ~ r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25)) )
      & ( ~ r2_hidden(X22,X24)
        | ~ r2_hidden(X23,X25)
        | r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(esk6_0,esk5_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk4_1(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk4_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_1(esk7_0),k2_zfmisc_1(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_1(esk6_0),X1),k2_zfmisc_1(esk6_0,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk4_1(esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k4_tarski(esk1_3(esk7_0,k2_relat_1(esk7_0),esk8_0),esk8_0),k2_zfmisc_1(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk6_0,esk5_0))
    | r2_hidden(esk4_1(esk7_0),k2_zfmisc_1(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_1(esk6_0),esk4_1(esk5_0)),k2_zfmisc_1(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk6_0,esk5_0))
    | r2_hidden(k4_tarski(esk1_3(esk7_0,k2_relat_1(esk7_0),esk8_0),esk8_0),k2_zfmisc_1(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk4_1(esk7_0),k2_zfmisc_1(esk6_0,esk5_0))
    | ~ r2_hidden(X1,k2_zfmisc_1(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk4_1(k2_zfmisc_1(esk6_0,esk5_0)),k2_zfmisc_1(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_3(esk7_0,k2_relat_1(esk7_0),esk8_0),esk8_0),k2_zfmisc_1(esk6_0,esk5_0))
    | ~ r2_hidden(X1,k2_zfmisc_1(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk4_1(esk7_0),k2_zfmisc_1(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k2_relset_1(esk6_0,esk5_0,esk7_0))
    | ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X1,esk8_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_52,plain,(
    ! [X26,X27] :
      ( ~ r2_hidden(X26,X27)
      | m1_subset_1(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_3(esk7_0,k2_relat_1(esk7_0),esk8_0),esk8_0),k2_zfmisc_1(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X1,esk8_0),esk7_0)
    | ~ r2_hidden(esk8_0,k2_relat_1(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_23])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,k2_relat_1(esk7_0),esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X1,esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_29])])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk1_3(esk7_0,k2_relat_1(esk7_0),esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_32])]),
    [proof]).

%------------------------------------------------------------------------------
