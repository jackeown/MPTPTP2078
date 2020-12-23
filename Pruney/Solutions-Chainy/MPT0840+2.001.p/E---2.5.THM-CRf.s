%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:41 EST 2020

% Result     : Theorem 18.98s
% Output     : CNFRefutation 18.98s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 963 expanded)
%              Number of clauses        :   48 ( 399 expanded)
%              Number of leaves         :    8 ( 224 expanded)
%              Depth                    :   18
%              Number of atoms          :  229 (5865 expanded)
%              Number of equality atoms :   15 ( 258 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_relset_1)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,plain,(
    ! [X36,X37,X38,X39,X40,X41] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | k4_relset_1(X36,X37,X38,X39,X40,X41) = k5_relat_1(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

fof(c_0_10,negated_conjecture,(
    ! [X49] :
      ( ~ v1_xboole_0(esk5_0)
      & ~ v1_xboole_0(esk6_0)
      & ~ v1_xboole_0(esk7_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & ( ~ r2_hidden(k4_tarski(esk10_0,esk11_0),k4_relset_1(esk5_0,esk6_0,esk6_0,esk7_0,esk8_0,esk9_0))
        | ~ m1_subset_1(X49,esk6_0)
        | ~ r2_hidden(k4_tarski(esk10_0,X49),esk8_0)
        | ~ r2_hidden(k4_tarski(X49,esk11_0),esk9_0) )
      & ( m1_subset_1(esk12_0,esk6_0)
        | r2_hidden(k4_tarski(esk10_0,esk11_0),k4_relset_1(esk5_0,esk6_0,esk6_0,esk7_0,esk8_0,esk9_0)) )
      & ( r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0)
        | r2_hidden(k4_tarski(esk10_0,esk11_0),k4_relset_1(esk5_0,esk6_0,esk6_0,esk7_0,esk8_0,esk9_0)) )
      & ( r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0)
        | r2_hidden(k4_tarski(esk10_0,esk11_0),k4_relset_1(esk5_0,esk6_0,esk6_0,esk7_0,esk8_0,esk9_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).

cnf(c_0_11,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X18,X19,X20,X21,X22,X24,X25,X26,X29] :
      ( ( r2_hidden(k4_tarski(X21,esk1_5(X18,X19,X20,X21,X22)),X18)
        | ~ r2_hidden(k4_tarski(X21,X22),X20)
        | X20 != k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk1_5(X18,X19,X20,X21,X22),X22),X19)
        | ~ r2_hidden(k4_tarski(X21,X22),X20)
        | X20 != k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X24,X26),X18)
        | ~ r2_hidden(k4_tarski(X26,X25),X19)
        | r2_hidden(k4_tarski(X24,X25),X20)
        | X20 != k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(esk2_3(X18,X19,X20),esk3_3(X18,X19,X20)),X20)
        | ~ r2_hidden(k4_tarski(esk2_3(X18,X19,X20),X29),X18)
        | ~ r2_hidden(k4_tarski(X29,esk3_3(X18,X19,X20)),X19)
        | X20 = k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk2_3(X18,X19,X20),esk4_3(X18,X19,X20)),X18)
        | r2_hidden(k4_tarski(esk2_3(X18,X19,X20),esk3_3(X18,X19,X20)),X20)
        | X20 = k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk4_3(X18,X19,X20),esk3_3(X18,X19,X20)),X19)
        | r2_hidden(k4_tarski(esk2_3(X18,X19,X20),esk3_3(X18,X19,X20)),X20)
        | X20 = k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_14,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X31)
      | ~ v1_relat_1(X32)
      | v1_relat_1(k5_relat_1(X31,X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_15,negated_conjecture,
    ( k4_relset_1(X1,X2,esk6_0,esk7_0,X3,esk9_0) = k5_relat_1(X3,esk9_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | v1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,esk1_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0)
    | r2_hidden(k4_tarski(esk10_0,esk11_0),k4_relset_1(esk5_0,esk6_0,esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( k4_relset_1(esk5_0,esk6_0,esk6_0,esk7_0,esk8_0,esk9_0) = k5_relat_1(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | ~ r2_hidden(X15,X14)
      | r2_hidden(X15,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(X1,esk1_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]),c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk11_0),k5_relat_1(esk8_0,esk9_0))
    | r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_16])).

cnf(c_0_28,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0)),esk8_0)
    | r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(esk1_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_31,plain,(
    ! [X9,X10,X11,X12] :
      ( ( r2_hidden(X9,X11)
        | ~ r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X11,X12)) )
      & ( r2_hidden(X10,X12)
        | ~ r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X11,X12)) )
      & ( ~ r2_hidden(X9,X11)
        | ~ r2_hidden(X10,X12)
        | r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X11,X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0)),X1)
    | r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk10_0,esk11_0),k4_relset_1(esk5_0,esk6_0,esk6_0,esk7_0,esk8_0,esk9_0))
    | ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(esk10_0,X1),esk8_0)
    | ~ r2_hidden(k4_tarski(X1,esk11_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(esk1_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]),c_0_19])).

fof(c_0_35,plain,(
    ! [X16,X17] :
      ( ~ r2_hidden(X16,X17)
      | m1_subset_1(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0)),k2_zfmisc_1(esk5_0,esk6_0))
    | r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(esk10_0,esk11_0),k5_relat_1(esk8_0,esk9_0))
    | ~ r2_hidden(k4_tarski(X1,esk11_0),esk9_0)
    | ~ r2_hidden(k4_tarski(esk10_0,X1),esk8_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0),esk11_0),esk9_0)
    | r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0),esk6_0)
    | r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0)
    | ~ m1_subset_1(esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_25]),c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0)
    | r2_hidden(k4_tarski(esk10_0,esk11_0),k4_relset_1(esk5_0,esk6_0,esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk11_0),k5_relat_1(esk8_0,esk9_0))
    | r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_43,c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(esk12_0,esk11_0),X1)
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0)),esk8_0)
    | r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_45]),c_0_26]),c_0_27])])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k4_tarski(esk12_0,esk11_0),k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_12])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0)),X1)
    | r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk12_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0)),k2_zfmisc_1(esk5_0,esk6_0))
    | r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0),esk11_0),esk9_0)
    | r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_45]),c_0_26]),c_0_27])])).

cnf(c_0_54,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_55,negated_conjecture,
    ( ~ m1_subset_1(esk12_0,esk6_0)
    | ~ r2_hidden(k4_tarski(esk10_0,esk11_0),k5_relat_1(esk8_0,esk9_0))
    | ~ r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk12_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0),esk6_0)
    | r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0)
    | ~ m1_subset_1(esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_53]),c_0_45]),c_0_47])).

cnf(c_0_59,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X5,X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_54]),c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk10_0,esk11_0),k5_relat_1(esk8_0,esk9_0))
    | ~ r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_57]),c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk11_0),k5_relat_1(X2,esk9_0))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,esk12_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_44]),c_0_26])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk10_0,esk11_0),k5_relat_1(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_61]),c_0_27])]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 18.98/19.14  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S08BA
% 18.98/19.14  # and selection function SelectCQPrecWNTNp.
% 18.98/19.14  #
% 18.98/19.14  # Preprocessing time       : 0.028 s
% 18.98/19.14  # Presaturation interreduction done
% 18.98/19.14  
% 18.98/19.14  # Proof found!
% 18.98/19.14  # SZS status Theorem
% 18.98/19.14  # SZS output start CNFRefutation
% 18.98/19.14  fof(t51_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>![X6, X7]:(r2_hidden(k4_tarski(X6,X7),k4_relset_1(X1,X2,X2,X3,X4,X5))<=>?[X8]:((m1_subset_1(X8,X2)&r2_hidden(k4_tarski(X6,X8),X4))&r2_hidden(k4_tarski(X8,X7),X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_relset_1)).
% 18.98/19.14  fof(redefinition_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k4_relset_1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 18.98/19.14  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 18.98/19.14  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 18.98/19.14  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 18.98/19.14  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 18.98/19.14  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 18.98/19.14  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 18.98/19.14  fof(c_0_8, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>![X6, X7]:(r2_hidden(k4_tarski(X6,X7),k4_relset_1(X1,X2,X2,X3,X4,X5))<=>?[X8]:((m1_subset_1(X8,X2)&r2_hidden(k4_tarski(X6,X8),X4))&r2_hidden(k4_tarski(X8,X7),X5))))))))), inference(assume_negation,[status(cth)],[t51_relset_1])).
% 18.98/19.14  fof(c_0_9, plain, ![X36, X37, X38, X39, X40, X41]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|k4_relset_1(X36,X37,X38,X39,X40,X41)=k5_relat_1(X40,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).
% 18.98/19.14  fof(c_0_10, negated_conjecture, ![X49]:(~v1_xboole_0(esk5_0)&(~v1_xboole_0(esk6_0)&(~v1_xboole_0(esk7_0)&(m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))&(m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))&((~r2_hidden(k4_tarski(esk10_0,esk11_0),k4_relset_1(esk5_0,esk6_0,esk6_0,esk7_0,esk8_0,esk9_0))|(~m1_subset_1(X49,esk6_0)|~r2_hidden(k4_tarski(esk10_0,X49),esk8_0)|~r2_hidden(k4_tarski(X49,esk11_0),esk9_0)))&(((m1_subset_1(esk12_0,esk6_0)|r2_hidden(k4_tarski(esk10_0,esk11_0),k4_relset_1(esk5_0,esk6_0,esk6_0,esk7_0,esk8_0,esk9_0)))&(r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0)|r2_hidden(k4_tarski(esk10_0,esk11_0),k4_relset_1(esk5_0,esk6_0,esk6_0,esk7_0,esk8_0,esk9_0))))&(r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0)|r2_hidden(k4_tarski(esk10_0,esk11_0),k4_relset_1(esk5_0,esk6_0,esk6_0,esk7_0,esk8_0,esk9_0)))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).
% 18.98/19.14  cnf(c_0_11, plain, (k4_relset_1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 18.98/19.14  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 18.98/19.14  fof(c_0_13, plain, ![X18, X19, X20, X21, X22, X24, X25, X26, X29]:((((r2_hidden(k4_tarski(X21,esk1_5(X18,X19,X20,X21,X22)),X18)|~r2_hidden(k4_tarski(X21,X22),X20)|X20!=k5_relat_1(X18,X19)|~v1_relat_1(X20)|~v1_relat_1(X19)|~v1_relat_1(X18))&(r2_hidden(k4_tarski(esk1_5(X18,X19,X20,X21,X22),X22),X19)|~r2_hidden(k4_tarski(X21,X22),X20)|X20!=k5_relat_1(X18,X19)|~v1_relat_1(X20)|~v1_relat_1(X19)|~v1_relat_1(X18)))&(~r2_hidden(k4_tarski(X24,X26),X18)|~r2_hidden(k4_tarski(X26,X25),X19)|r2_hidden(k4_tarski(X24,X25),X20)|X20!=k5_relat_1(X18,X19)|~v1_relat_1(X20)|~v1_relat_1(X19)|~v1_relat_1(X18)))&((~r2_hidden(k4_tarski(esk2_3(X18,X19,X20),esk3_3(X18,X19,X20)),X20)|(~r2_hidden(k4_tarski(esk2_3(X18,X19,X20),X29),X18)|~r2_hidden(k4_tarski(X29,esk3_3(X18,X19,X20)),X19))|X20=k5_relat_1(X18,X19)|~v1_relat_1(X20)|~v1_relat_1(X19)|~v1_relat_1(X18))&((r2_hidden(k4_tarski(esk2_3(X18,X19,X20),esk4_3(X18,X19,X20)),X18)|r2_hidden(k4_tarski(esk2_3(X18,X19,X20),esk3_3(X18,X19,X20)),X20)|X20=k5_relat_1(X18,X19)|~v1_relat_1(X20)|~v1_relat_1(X19)|~v1_relat_1(X18))&(r2_hidden(k4_tarski(esk4_3(X18,X19,X20),esk3_3(X18,X19,X20)),X19)|r2_hidden(k4_tarski(esk2_3(X18,X19,X20),esk3_3(X18,X19,X20)),X20)|X20=k5_relat_1(X18,X19)|~v1_relat_1(X20)|~v1_relat_1(X19)|~v1_relat_1(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 18.98/19.14  fof(c_0_14, plain, ![X31, X32]:(~v1_relat_1(X31)|~v1_relat_1(X32)|v1_relat_1(k5_relat_1(X31,X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 18.98/19.14  cnf(c_0_15, negated_conjecture, (k4_relset_1(X1,X2,esk6_0,esk7_0,X3,esk9_0)=k5_relat_1(X3,esk9_0)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 18.98/19.14  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 18.98/19.14  fof(c_0_17, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|v1_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 18.98/19.14  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X1,esk1_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 18.98/19.14  cnf(c_0_19, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 18.98/19.14  cnf(c_0_20, negated_conjecture, (r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0)|r2_hidden(k4_tarski(esk10_0,esk11_0),k4_relset_1(esk5_0,esk6_0,esk6_0,esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 18.98/19.14  cnf(c_0_21, negated_conjecture, (k4_relset_1(esk5_0,esk6_0,esk6_0,esk7_0,esk8_0,esk9_0)=k5_relat_1(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 18.98/19.14  cnf(c_0_22, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 18.98/19.14  fof(c_0_23, plain, ![X13, X14, X15]:(~m1_subset_1(X14,k1_zfmisc_1(X13))|(~r2_hidden(X15,X14)|r2_hidden(X15,X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 18.98/19.14  cnf(c_0_24, plain, (r2_hidden(k4_tarski(X1,esk1_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]), c_0_19])).
% 18.98/19.14  cnf(c_0_25, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk11_0),k5_relat_1(esk8_0,esk9_0))|r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 18.98/19.14  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_22, c_0_12])).
% 18.98/19.14  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_22, c_0_16])).
% 18.98/19.14  cnf(c_0_28, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 18.98/19.14  cnf(c_0_29, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0)),esk8_0)|r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])])).
% 18.98/19.14  cnf(c_0_30, plain, (r2_hidden(k4_tarski(esk1_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 18.98/19.14  fof(c_0_31, plain, ![X9, X10, X11, X12]:(((r2_hidden(X9,X11)|~r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X11,X12)))&(r2_hidden(X10,X12)|~r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X11,X12))))&(~r2_hidden(X9,X11)|~r2_hidden(X10,X12)|r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X11,X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 18.98/19.14  cnf(c_0_32, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0)),X1)|r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0)|~m1_subset_1(esk8_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 18.98/19.14  cnf(c_0_33, negated_conjecture, (~r2_hidden(k4_tarski(esk10_0,esk11_0),k4_relset_1(esk5_0,esk6_0,esk6_0,esk7_0,esk8_0,esk9_0))|~m1_subset_1(X1,esk6_0)|~r2_hidden(k4_tarski(esk10_0,X1),esk8_0)|~r2_hidden(k4_tarski(X1,esk11_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 18.98/19.14  cnf(c_0_34, plain, (r2_hidden(k4_tarski(esk1_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]), c_0_19])).
% 18.98/19.14  fof(c_0_35, plain, ![X16, X17]:(~r2_hidden(X16,X17)|m1_subset_1(X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 18.98/19.14  cnf(c_0_36, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 18.98/19.14  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0)),k2_zfmisc_1(esk5_0,esk6_0))|r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0)), inference(spm,[status(thm)],[c_0_32, c_0_16])).
% 18.98/19.14  cnf(c_0_38, negated_conjecture, (~m1_subset_1(X1,esk6_0)|~r2_hidden(k4_tarski(esk10_0,esk11_0),k5_relat_1(esk8_0,esk9_0))|~r2_hidden(k4_tarski(X1,esk11_0),esk9_0)|~r2_hidden(k4_tarski(esk10_0,X1),esk8_0)), inference(rw,[status(thm)],[c_0_33, c_0_21])).
% 18.98/19.14  cnf(c_0_39, negated_conjecture, (r2_hidden(k4_tarski(esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0),esk11_0),esk9_0)|r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_25]), c_0_26]), c_0_27])])).
% 18.98/19.14  cnf(c_0_40, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 18.98/19.14  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0),esk6_0)|r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 18.98/19.14  cnf(c_0_42, negated_conjecture, (r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0)|~m1_subset_1(esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_25]), c_0_29])).
% 18.98/19.14  cnf(c_0_43, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0)|r2_hidden(k4_tarski(esk10_0,esk11_0),k4_relset_1(esk5_0,esk6_0,esk6_0,esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 18.98/19.14  cnf(c_0_44, negated_conjecture, (r2_hidden(k4_tarski(esk12_0,esk11_0),esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 18.98/19.14  cnf(c_0_45, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk11_0),k5_relat_1(esk8_0,esk9_0))|r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0)), inference(rw,[status(thm)],[c_0_43, c_0_21])).
% 18.98/19.14  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_tarski(esk12_0,esk11_0),X1)|~m1_subset_1(esk9_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_28, c_0_44])).
% 18.98/19.14  cnf(c_0_47, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0)),esk8_0)|r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_45]), c_0_26]), c_0_27])])).
% 18.98/19.14  cnf(c_0_48, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 18.98/19.14  cnf(c_0_49, negated_conjecture, (r2_hidden(k4_tarski(esk12_0,esk11_0),k2_zfmisc_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_46, c_0_12])).
% 18.98/19.14  cnf(c_0_50, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0)),X1)|r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0)|~m1_subset_1(esk8_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_28, c_0_47])).
% 18.98/19.14  cnf(c_0_51, negated_conjecture, (r2_hidden(esk12_0,esk6_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 18.98/19.14  cnf(c_0_52, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0)),k2_zfmisc_1(esk5_0,esk6_0))|r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0)), inference(spm,[status(thm)],[c_0_50, c_0_16])).
% 18.98/19.14  cnf(c_0_53, negated_conjecture, (r2_hidden(k4_tarski(esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0),esk11_0),esk9_0)|r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_45]), c_0_26]), c_0_27])])).
% 18.98/19.14  cnf(c_0_54, plain, (r2_hidden(k4_tarski(X1,X4),X6)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X2,X4),X5)|X6!=k5_relat_1(X3,X5)|~v1_relat_1(X6)|~v1_relat_1(X5)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 18.98/19.14  cnf(c_0_55, negated_conjecture, (~m1_subset_1(esk12_0,esk6_0)|~r2_hidden(k4_tarski(esk10_0,esk11_0),k5_relat_1(esk8_0,esk9_0))|~r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0)), inference(spm,[status(thm)],[c_0_38, c_0_44])).
% 18.98/19.14  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk12_0,esk6_0)), inference(spm,[status(thm)],[c_0_40, c_0_51])).
% 18.98/19.14  cnf(c_0_57, negated_conjecture, (r2_hidden(esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0),esk6_0)|r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0)), inference(spm,[status(thm)],[c_0_36, c_0_52])).
% 18.98/19.14  cnf(c_0_58, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0)|~m1_subset_1(esk1_5(esk8_0,esk9_0,k5_relat_1(esk8_0,esk9_0),esk10_0,esk11_0),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_53]), c_0_45]), c_0_47])).
% 18.98/19.14  cnf(c_0_59, plain, (r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))|~v1_relat_1(X4)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X5,X2),X4)|~r2_hidden(k4_tarski(X1,X5),X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_54]), c_0_19])).
% 18.98/19.14  cnf(c_0_60, negated_conjecture, (~r2_hidden(k4_tarski(esk10_0,esk11_0),k5_relat_1(esk8_0,esk9_0))|~r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56])])).
% 18.98/19.14  cnf(c_0_61, negated_conjecture, (r2_hidden(k4_tarski(esk10_0,esk12_0),esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_57]), c_0_58])).
% 18.98/19.14  cnf(c_0_62, negated_conjecture, (r2_hidden(k4_tarski(X1,esk11_0),k5_relat_1(X2,esk9_0))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,esk12_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_44]), c_0_26])])).
% 18.98/19.14  cnf(c_0_63, negated_conjecture, (~r2_hidden(k4_tarski(esk10_0,esk11_0),k5_relat_1(esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61])])).
% 18.98/19.14  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_61]), c_0_27])]), c_0_63]), ['proof']).
% 18.98/19.14  # SZS output end CNFRefutation
% 18.98/19.14  # Proof object total steps             : 65
% 18.98/19.14  # Proof object clause steps            : 48
% 18.98/19.14  # Proof object formula steps           : 17
% 18.98/19.14  # Proof object conjectures             : 38
% 18.98/19.14  # Proof object clause conjectures      : 35
% 18.98/19.14  # Proof object formula conjectures     : 3
% 18.98/19.14  # Proof object initial clauses used    : 15
% 18.98/19.14  # Proof object initial formulas used   : 8
% 18.98/19.14  # Proof object generating inferences   : 25
% 18.98/19.14  # Proof object simplifying inferences  : 36
% 18.98/19.14  # Training examples: 0 positive, 0 negative
% 18.98/19.14  # Parsed axioms                        : 8
% 18.98/19.14  # Removed by relevancy pruning/SinE    : 0
% 18.98/19.14  # Initial clauses                      : 23
% 18.98/19.14  # Removed in clause preprocessing      : 0
% 18.98/19.14  # Initial clauses in saturation        : 23
% 18.98/19.14  # Processed clauses                    : 5402
% 18.98/19.14  # ...of these trivial                  : 0
% 18.98/19.14  # ...subsumed                          : 339
% 18.98/19.14  # ...remaining for further processing  : 5062
% 18.98/19.14  # Other redundant clauses eliminated   : 3
% 18.98/19.14  # Clauses deleted for lack of memory   : 0
% 18.98/19.14  # Backward-subsumed                    : 91
% 18.98/19.14  # Backward-rewritten                   : 280
% 18.98/19.14  # Generated clauses                    : 1179107
% 18.98/19.14  # ...of the previous two non-trivial   : 1176348
% 18.98/19.14  # Contextual simplify-reflections      : 63
% 18.98/19.14  # Paramodulations                      : 1179104
% 18.98/19.14  # Factorizations                       : 0
% 18.98/19.14  # Equation resolutions                 : 3
% 18.98/19.14  # Propositional unsat checks           : 0
% 18.98/19.14  #    Propositional check models        : 0
% 18.98/19.14  #    Propositional check unsatisfiable : 0
% 18.98/19.14  #    Propositional clauses             : 0
% 18.98/19.14  #    Propositional clauses after purity: 0
% 18.98/19.14  #    Propositional unsat core size     : 0
% 18.98/19.14  #    Propositional preprocessing time  : 0.000
% 18.98/19.14  #    Propositional encoding time       : 0.000
% 18.98/19.14  #    Propositional solver time         : 0.000
% 18.98/19.14  #    Success case prop preproc time    : 0.000
% 18.98/19.14  #    Success case prop encoding time   : 0.000
% 18.98/19.14  #    Success case prop solver time     : 0.000
% 18.98/19.14  # Current number of processed clauses  : 4665
% 18.98/19.14  #    Positive orientable unit clauses  : 2639
% 18.98/19.14  #    Positive unorientable unit clauses: 0
% 18.98/19.14  #    Negative unit clauses             : 4
% 18.98/19.14  #    Non-unit-clauses                  : 2022
% 18.98/19.14  # Current number of unprocessed clauses: 1170375
% 18.98/19.14  # ...number of literals in the above   : 10463050
% 18.98/19.14  # Current number of archived formulas  : 0
% 18.98/19.14  # Current number of archived clauses   : 394
% 18.98/19.14  # Clause-clause subsumption calls (NU) : 520595
% 18.98/19.14  # Rec. Clause-clause subsumption calls : 179070
% 18.98/19.14  # Non-unit clause-clause subsumptions  : 421
% 18.98/19.14  # Unit Clause-clause subsumption calls : 153479
% 18.98/19.14  # Rewrite failures with RHS unbound    : 0
% 18.98/19.14  # BW rewrite match attempts            : 240364
% 18.98/19.14  # BW rewrite match successes           : 74
% 18.98/19.14  # Condensation attempts                : 0
% 18.98/19.14  # Condensation successes               : 0
% 18.98/19.14  # Termbank termtop insertions          : 53121202
% 18.98/19.20  
% 18.98/19.20  # -------------------------------------------------
% 18.98/19.20  # User time                : 18.234 s
% 18.98/19.20  # System time              : 0.623 s
% 18.98/19.20  # Total time               : 18.857 s
% 18.98/19.20  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
