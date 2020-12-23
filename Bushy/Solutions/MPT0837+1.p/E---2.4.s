%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relset_1__t48_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:10 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   41 (  90 expanded)
%              Number of clauses        :   24 (  40 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  123 ( 373 expanded)
%              Number of equality atoms :   11 (  42 expanded)
%              Maximal formula depth    :   15 (   5 average)
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
    file('/export/starexec/sandbox/benchmark/relset_1__t48_relset_1.p',t48_relset_1)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t48_relset_1.p',t106_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t48_relset_1.p',t2_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t48_relset_1.p',t4_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t48_relset_1.p',t5_subset)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t48_relset_1.p',redefinition_k2_relset_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t48_relset_1.p',d5_relat_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t48_relset_1.p',t1_subset)).

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,plain,(
    ! [X33,X34,X35,X36] :
      ( ( r2_hidden(X33,X35)
        | ~ r2_hidden(k4_tarski(X33,X34),k2_zfmisc_1(X35,X36)) )
      & ( r2_hidden(X34,X36)
        | ~ r2_hidden(k4_tarski(X33,X34),k2_zfmisc_1(X35,X36)) )
      & ( ~ r2_hidden(X33,X35)
        | ~ r2_hidden(X34,X36)
        | r2_hidden(k4_tarski(X33,X34),k2_zfmisc_1(X35,X36)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

fof(c_0_10,plain,(
    ! [X42,X43] :
      ( ~ m1_subset_1(X42,X43)
      | v1_xboole_0(X43)
      | r2_hidden(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_11,plain,(
    ! [X46,X47,X48] :
      ( ~ r2_hidden(X46,X47)
      | ~ m1_subset_1(X47,k1_zfmisc_1(X48))
      | m1_subset_1(X46,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_12,negated_conjecture,(
    ! [X10] :
      ( ~ v1_xboole_0(esk1_0)
      & ~ v1_xboole_0(esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
      & ( ~ r2_hidden(esk4_0,k2_relset_1(esk2_0,esk1_0,esk3_0))
        | ~ m1_subset_1(X10,esk2_0)
        | ~ r2_hidden(k4_tarski(X10,esk4_0),esk3_0) )
      & ( m1_subset_1(esk5_0,esk2_0)
        | r2_hidden(esk4_0,k2_relset_1(esk2_0,esk1_0,esk3_0)) )
      & ( r2_hidden(k4_tarski(esk5_0,esk4_0),esk3_0)
        | r2_hidden(esk4_0,k2_relset_1(esk2_0,esk1_0,esk3_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).

fof(c_0_13,plain,(
    ! [X49,X50,X51] :
      ( ~ r2_hidden(X49,X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(X51))
      | ~ v1_xboole_0(X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_14,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k2_relset_1(X30,X31,X32) = k2_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_15,plain,(
    ! [X14,X15,X16,X18,X19,X20,X21,X23] :
      ( ( ~ r2_hidden(X16,X15)
        | r2_hidden(k4_tarski(esk6_3(X14,X15,X16),X16),X14)
        | X15 != k2_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(X19,X18),X14)
        | r2_hidden(X18,X15)
        | X15 != k2_relat_1(X14) )
      & ( ~ r2_hidden(esk7_2(X20,X21),X21)
        | ~ r2_hidden(k4_tarski(X23,esk7_2(X20,X21)),X20)
        | X21 = k2_relat_1(X20) )
      & ( r2_hidden(esk7_2(X20,X21),X21)
        | r2_hidden(k4_tarski(esk8_2(X20,X21),esk7_2(X20,X21)),X20)
        | X21 = k2_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(k4_tarski(X1,X4),k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(esk2_0,esk1_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(X1,esk3_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk2_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k2_relset_1(esk2_0,esk1_0,esk3_0))
    | ~ m1_subset_1(X1,esk2_0)
    | ~ r2_hidden(k4_tarski(X1,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( k2_relset_1(esk2_0,esk1_0,esk3_0) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk4_0),esk3_0)
    | r2_hidden(esk4_0,k2_relset_1(esk2_0,esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_31,plain,(
    ! [X37,X38] :
      ( ~ r2_hidden(X37,X38)
      | m1_subset_1(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk4_0),esk3_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk4_0,k2_relat_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_28]),c_0_29])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk6_3(esk3_0,k2_relat_1(esk3_0),X1),esk2_0)
    | ~ r2_hidden(X1,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( ~ m1_subset_1(esk6_3(esk3_0,k2_relat_1(esk3_0),esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_35])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk6_3(esk3_0,k2_relat_1(esk3_0),X1),esk2_0)
    | ~ r2_hidden(X1,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
