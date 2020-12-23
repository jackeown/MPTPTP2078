%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0840+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 267 expanded)
%              Number of clauses        :   44 ( 108 expanded)
%              Number of leaves         :   11 (  65 expanded)
%              Depth                    :   19
%              Number of atoms          :  259 (1584 expanded)
%              Number of equality atoms :   22 (  61 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                 => ! [X5] :
                      ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
                     => ! [X6,X7] :
                          ( r2_hidden(k4_tarski(X6,X7),k4_relset_1(X1,X2,X2,X3,X4,X5))
                        <=> ? [X8] :
                              ( m1_subset_1(X8,X2)
                              & r2_hidden(k4_tarski(X6,X8),X4)
                              & r2_hidden(k4_tarski(X8,X7),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ~ v1_xboole_0(X3)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                   => ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
                       => ! [X6,X7] :
                            ( r2_hidden(k4_tarski(X6,X7),k4_relset_1(X1,X2,X2,X3,X4,X5))
                          <=> ? [X8] :
                                ( m1_subset_1(X8,X2)
                                & r2_hidden(k4_tarski(X6,X8),X4)
                                & r2_hidden(k4_tarski(X8,X7),X5) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_relset_1])).

fof(c_0_12,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | v1_relat_1(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_13,negated_conjecture,(
    ! [X55] :
      ( ~ v1_xboole_0(esk6_0)
      & ~ v1_xboole_0(esk7_0)
      & ~ v1_xboole_0(esk8_0)
      & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))
      & ( ~ r2_hidden(k4_tarski(esk11_0,esk12_0),k4_relset_1(esk6_0,esk7_0,esk7_0,esk8_0,esk9_0,esk10_0))
        | ~ m1_subset_1(X55,esk7_0)
        | ~ r2_hidden(k4_tarski(esk11_0,X55),esk9_0)
        | ~ r2_hidden(k4_tarski(X55,esk12_0),esk10_0) )
      & ( m1_subset_1(esk13_0,esk7_0)
        | r2_hidden(k4_tarski(esk11_0,esk12_0),k4_relset_1(esk6_0,esk7_0,esk7_0,esk8_0,esk9_0,esk10_0)) )
      & ( r2_hidden(k4_tarski(esk11_0,esk13_0),esk9_0)
        | r2_hidden(k4_tarski(esk11_0,esk12_0),k4_relset_1(esk6_0,esk7_0,esk7_0,esk8_0,esk9_0,esk10_0)) )
      & ( r2_hidden(k4_tarski(esk13_0,esk12_0),esk10_0)
        | r2_hidden(k4_tarski(esk11_0,esk12_0),k4_relset_1(esk6_0,esk7_0,esk7_0,esk8_0,esk9_0,esk10_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])])).

fof(c_0_14,plain,(
    ! [X12,X13,X14,X15,X16,X18,X19,X20,X23] :
      ( ( r2_hidden(k4_tarski(X15,esk1_5(X12,X13,X14,X15,X16)),X12)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k5_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk1_5(X12,X13,X14,X15,X16),X16),X13)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k5_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(X18,X20),X12)
        | ~ r2_hidden(k4_tarski(X20,X19),X13)
        | r2_hidden(k4_tarski(X18,X19),X14)
        | X14 != k5_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)
        | ~ r2_hidden(k4_tarski(esk2_3(X12,X13,X14),X23),X12)
        | ~ r2_hidden(k4_tarski(X23,esk3_3(X12,X13,X14)),X13)
        | X14 = k5_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk4_3(X12,X13,X14)),X12)
        | r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)
        | X14 = k5_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk4_3(X12,X13,X14),esk3_3(X12,X13,X14)),X13)
        | r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)
        | X14 = k5_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

cnf(c_0_15,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k4_tarski(esk13_0,esk12_0),esk10_0)
    | r2_hidden(k4_tarski(esk11_0,esk12_0),k4_relset_1(esk6_0,esk7_0,esk7_0,esk8_0,esk9_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k4_tarski(esk11_0,esk12_0),k4_relset_1(esk6_0,esk7_0,esk7_0,esk8_0,esk9_0,esk10_0))
    | r2_hidden(k4_tarski(X1,esk12_0),X2)
    | X2 != k5_relat_1(X3,esk10_0)
    | ~ r2_hidden(k4_tarski(X1,esk13_0),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k4_tarski(esk11_0,esk13_0),esk9_0)
    | r2_hidden(k4_tarski(esk11_0,esk12_0),k4_relset_1(esk6_0,esk7_0,esk7_0,esk8_0,esk9_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_20])).

fof(c_0_24,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ v1_relat_1(X26)
      | v1_relat_1(k5_relat_1(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(esk11_0,esk12_0),k4_relset_1(esk6_0,esk7_0,esk7_0,esk8_0,esk9_0,esk10_0))
    | r2_hidden(k4_tarski(esk11_0,esk12_0),X1)
    | X1 != k5_relat_1(esk9_0,esk10_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_26,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_27,plain,(
    ! [X29,X30,X31,X32,X33,X34] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k4_relset_1(X29,X30,X31,X32,X33,X34) = k5_relat_1(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk11_0,esk12_0),k4_relset_1(esk6_0,esk7_0,esk7_0,esk8_0,esk9_0,esk10_0))
    | r2_hidden(k4_tarski(esk11_0,esk12_0),k5_relat_1(X1,X2))
    | k5_relat_1(X1,X2) != k5_relat_1(esk9_0,esk10_0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk11_0,esk12_0),k4_relset_1(esk6_0,esk7_0,esk7_0,esk8_0,esk9_0,esk10_0))
    | ~ m1_subset_1(X1,esk7_0)
    | ~ r2_hidden(k4_tarski(esk11_0,X1),esk9_0)
    | ~ r2_hidden(k4_tarski(X1,esk12_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(esk11_0,esk12_0),k4_relset_1(esk6_0,esk7_0,esk7_0,esk8_0,esk9_0,esk10_0))
    | r2_hidden(k4_tarski(esk11_0,esk12_0),k5_relat_1(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_19]),c_0_23])])).

fof(c_0_32,plain,(
    ! [X43,X44,X45] :
      ( ~ r2_hidden(X43,X44)
      | ~ m1_subset_1(X44,k1_zfmisc_1(X45))
      | m1_subset_1(X43,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk11_0,esk12_0),k5_relat_1(esk9_0,esk10_0))
    | ~ r2_hidden(k4_tarski(X1,esk12_0),esk10_0)
    | ~ r2_hidden(k4_tarski(esk11_0,X1),esk9_0)
    | ~ m1_subset_1(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_16]),c_0_20])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(esk11_0,esk12_0),k5_relat_1(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_30]),c_0_16]),c_0_20])])).

fof(c_0_35,plain,(
    ! [X41,X42] :
      ( ~ m1_subset_1(X41,X42)
      | v1_xboole_0(X42)
      | r2_hidden(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk12_0),esk10_0)
    | ~ r2_hidden(k4_tarski(esk11_0,X1),esk9_0)
    | ~ m1_subset_1(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(esk1_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_39,plain,(
    ! [X39,X40] :
      ( ~ r2_hidden(X39,X40)
      | m1_subset_1(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(esk7_0,esk8_0))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( X1 != k5_relat_1(X2,esk10_0)
    | ~ r2_hidden(k4_tarski(esk11_0,esk1_5(X2,esk10_0,X1,X3,esk12_0)),esk9_0)
    | ~ r2_hidden(k4_tarski(X3,esk12_0),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ m1_subset_1(esk1_5(X2,esk10_0,X1,X3,esk12_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_19])])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_44,plain,(
    ! [X35,X36,X37,X38] :
      ( ( r2_hidden(X35,X37)
        | ~ r2_hidden(k4_tarski(X35,X36),k2_zfmisc_1(X37,X38)) )
      & ( r2_hidden(X36,X38)
        | ~ r2_hidden(k4_tarski(X35,X36),k2_zfmisc_1(X37,X38)) )
      & ( ~ r2_hidden(X35,X37)
        | ~ r2_hidden(X36,X38)
        | r2_hidden(k4_tarski(X35,X36),k2_zfmisc_1(X37,X38)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk7_0,esk8_0))
    | r2_hidden(X1,k2_zfmisc_1(esk7_0,esk8_0))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( X1 != k5_relat_1(X2,esk10_0)
    | ~ r2_hidden(k4_tarski(esk11_0,esk1_5(X2,esk10_0,X1,X3,esk12_0)),esk9_0)
    | ~ r2_hidden(esk1_5(X2,esk10_0,X1,X3,esk12_0),esk7_0)
    | ~ r2_hidden(k4_tarski(X3,esk12_0),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,plain,
    ( r2_hidden(k4_tarski(X1,esk1_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk7_0,esk8_0))
    | r2_hidden(k4_tarski(esk1_5(X1,esk10_0,X2,X3,X4),X4),k2_zfmisc_1(esk7_0,esk8_0))
    | X2 != k5_relat_1(X1,esk10_0)
    | ~ r2_hidden(k4_tarski(X3,X4),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_38]),c_0_19])])).

fof(c_0_50,plain,(
    ! [X46,X47] :
      ( ~ r2_hidden(X46,X47)
      | ~ v1_xboole_0(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_51,negated_conjecture,
    ( X1 != k5_relat_1(esk9_0,esk10_0)
    | ~ r2_hidden(esk1_5(esk9_0,esk10_0,X1,esk11_0,esk12_0),esk7_0)
    | ~ r2_hidden(k4_tarski(esk11_0,esk12_0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_23]),c_0_19])])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk7_0,esk8_0))
    | r2_hidden(esk1_5(X1,esk10_0,X2,X3,X4),esk7_0)
    | X2 != k5_relat_1(X1,esk10_0)
    | ~ r2_hidden(k4_tarski(X3,X4),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_54,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk7_0,esk8_0))
    | X1 != k5_relat_1(esk9_0,esk10_0)
    | ~ r2_hidden(k4_tarski(esk11_0,esk12_0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_23])])).

fof(c_0_56,plain,(
    ! [X27] : m1_subset_1(esk5_1(X27),X27) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_57,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk7_0,esk8_0))
    | ~ v1_relat_1(k5_relat_1(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_34])).

cnf(c_0_59,plain,
    ( m1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X2,esk7_0)
    | ~ v1_relat_1(k5_relat_1(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk5_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ v1_relat_1(k5_relat_1(esk9_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_26]),c_0_19]),c_0_23])])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_61]),c_0_65]),
    [proof]).

%------------------------------------------------------------------------------
