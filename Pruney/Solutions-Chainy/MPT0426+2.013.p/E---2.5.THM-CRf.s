%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:49 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 649 expanded)
%              Number of clauses        :   52 ( 277 expanded)
%              Number of leaves         :   13 ( 154 expanded)
%              Depth                    :   15
%              Number of atoms          :  211 (2513 expanded)
%              Number of equality atoms :   48 ( 404 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_setfam_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( r2_hidden(X2,X1)
       => ( r2_hidden(X2,k8_setfam_1(X1,X3))
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
             => r2_hidden(X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t43_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,X3)
          <=> r1_tarski(X2,k3_subset_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(idempotence_k8_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k8_subset_1(X1,X2,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k8_subset_1)).

fof(redefinition_k8_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k8_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_subset_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( r2_hidden(X2,X1)
         => ( r2_hidden(X2,k8_setfam_1(X1,X3))
          <=> ! [X4] :
                ( r2_hidden(X4,X3)
               => r2_hidden(X2,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t58_setfam_1])).

fof(c_0_14,plain,(
    ! [X50,X51] :
      ( ( r2_hidden(esk5_2(X50,X51),X50)
        | X50 = k1_xboole_0
        | r1_tarski(X51,k1_setfam_1(X50)) )
      & ( ~ r1_tarski(X51,esk5_2(X50,X51))
        | X50 = k1_xboole_0
        | r1_tarski(X51,k1_setfam_1(X50)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

fof(c_0_15,plain,(
    ! [X23,X24] :
      ( ( ~ r1_tarski(k1_tarski(X23),X24)
        | r2_hidden(X23,X24) )
      & ( ~ r2_hidden(X23,X24)
        | r1_tarski(k1_tarski(X23),X24) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_16,negated_conjecture,(
    ! [X57] :
      ( m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0)))
      & r2_hidden(esk7_0,esk6_0)
      & ( r2_hidden(esk9_0,esk8_0)
        | ~ r2_hidden(esk7_0,k8_setfam_1(esk6_0,esk8_0)) )
      & ( ~ r2_hidden(esk7_0,esk9_0)
        | ~ r2_hidden(esk7_0,k8_setfam_1(esk6_0,esk8_0)) )
      & ( r2_hidden(esk7_0,k8_setfam_1(esk6_0,esk8_0))
        | ~ r2_hidden(X57,esk8_0)
        | r2_hidden(esk7_0,X57) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])])).

fof(c_0_17,plain,(
    ! [X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k1_zfmisc_1(X41)))
      | k6_setfam_1(X41,X42) = k1_setfam_1(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

cnf(c_0_18,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk5_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk7_0,k8_setfam_1(esk6_0,esk8_0))
    | r2_hidden(esk7_0,X1)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X39,X40] :
      ( ( X40 = k1_xboole_0
        | k8_setfam_1(X39,X40) = k6_setfam_1(X39,X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k1_zfmisc_1(X39))) )
      & ( X40 != k1_xboole_0
        | k8_setfam_1(X39,X40) = X39
        | ~ m1_subset_1(X40,k1_zfmisc_1(k1_zfmisc_1(X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

cnf(c_0_23,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_tarski(X2),k1_setfam_1(X1))
    | ~ r2_hidden(X2,esk5_2(X1,k1_tarski(X2))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(esk8_0))
    | r2_hidden(esk7_0,k8_setfam_1(esk6_0,esk8_0))
    | r2_hidden(esk7_0,esk5_2(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( k6_setfam_1(esk6_0,esk8_0) = k1_setfam_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0)
    | ~ r2_hidden(esk7_0,k8_setfam_1(esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r1_tarski(k1_tarski(esk7_0),k1_setfam_1(esk8_0))
    | r2_hidden(esk7_0,k8_setfam_1(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k8_setfam_1(esk6_0,esk8_0) = k1_setfam_1(esk8_0)
    | esk8_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_28])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r1_tarski(k1_tarski(esk7_0),k1_setfam_1(esk8_0))
    | r2_hidden(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(esk9_0,esk8_0)
    | ~ r2_hidden(esk7_0,k1_setfam_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_31])).

fof(c_0_35,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_36,plain,(
    ! [X45,X46] :
      ( ~ r2_hidden(X45,X46)
      | r1_tarski(k1_setfam_1(X46),X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_37,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(esk9_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_38,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(esk7_0,k8_setfam_1(esk6_0,esk8_0))
    | r2_hidden(esk7_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_37])).

fof(c_0_41,plain,(
    ! [X43,X44] :
      ( ( ~ m1_subset_1(X43,k1_zfmisc_1(X44))
        | r1_tarski(X43,X44) )
      & ( ~ r1_tarski(X43,X44)
        | m1_subset_1(X43,k1_zfmisc_1(X44)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_42,plain,(
    ! [X38] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X38)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(X3))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(esk7_0,k1_setfam_1(esk8_0))
    | r2_hidden(esk7_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_31])).

fof(c_0_45,plain,(
    ! [X35,X36,X37] :
      ( ( ~ r1_xboole_0(X36,X37)
        | r1_tarski(X36,k3_subset_1(X35,X37))
        | ~ m1_subset_1(X37,k1_zfmisc_1(X35))
        | ~ m1_subset_1(X36,k1_zfmisc_1(X35)) )
      & ( ~ r1_tarski(X36,k3_subset_1(X35,X37))
        | r1_xboole_0(X36,X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(X35))
        | ~ m1_subset_1(X36,k1_zfmisc_1(X35)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(esk7_0,esk9_0)
    | ~ r2_hidden(esk7_0,k8_setfam_1(esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(esk7_0,esk9_0)
    | r2_hidden(esk7_0,X1)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_50,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | k8_subset_1(X25,X26,X26) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k8_subset_1])])])).

fof(c_0_51,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | k8_subset_1(X27,X28,X29) = k3_xboole_0(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_subset_1])])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r1_tarski(k1_tarski(esk7_0),k1_setfam_1(esk8_0))
    | ~ r2_hidden(esk7_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(esk7_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_37])).

cnf(c_0_56,plain,
    ( k8_subset_1(X2,X1,X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( k8_subset_1(X2,X1,X3) = k3_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_47])])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_61,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_62,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r1_tarski(k1_tarski(esk7_0),k1_setfam_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_63,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r1_xboole_0(X15,X16)
        | r2_hidden(esk3_2(X15,X16),k3_xboole_0(X15,X16)) )
      & ( ~ r2_hidden(X20,k3_xboole_0(X18,X19))
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_64,plain,
    ( k8_subset_1(X1,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_47])).

cnf(c_0_65,plain,
    ( k8_subset_1(X1,k1_xboole_0,X2) = k3_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_47])).

cnf(c_0_66,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | ~ r2_hidden(esk7_0,k1_setfam_1(esk8_0))
    | ~ r2_hidden(esk7_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_31])).

cnf(c_0_69,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(esk7_0,k1_setfam_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_62])).

cnf(c_0_70,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_73,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_55])).

cnf(c_0_75,plain,
    ( k8_setfam_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_70]),c_0_47])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_77,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_74]),c_0_74]),c_0_75]),c_0_76])]),c_0_77]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.31  % Computer   : n003.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 14:44:12 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  # Version: 2.5pre002
% 0.16/0.31  # No SInE strategy applied
% 0.16/0.31  # Trying AutoSched0 for 299 seconds
% 0.16/0.38  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.16/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.16/0.38  #
% 0.16/0.38  # Preprocessing time       : 0.028 s
% 0.16/0.38  # Presaturation interreduction done
% 0.16/0.38  
% 0.16/0.38  # Proof found!
% 0.16/0.38  # SZS status Theorem
% 0.16/0.38  # SZS output start CNFRefutation
% 0.16/0.38  fof(t58_setfam_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r2_hidden(X2,X1)=>(r2_hidden(X2,k8_setfam_1(X1,X3))<=>![X4]:(r2_hidden(X4,X3)=>r2_hidden(X2,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_setfam_1)).
% 0.16/0.38  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 0.16/0.38  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.16/0.38  fof(redefinition_k6_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k6_setfam_1(X1,X2)=k1_setfam_1(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 0.16/0.38  fof(d10_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((X2!=k1_xboole_0=>k8_setfam_1(X1,X2)=k6_setfam_1(X1,X2))&(X2=k1_xboole_0=>k8_setfam_1(X1,X2)=X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 0.16/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.16/0.38  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.16/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.16/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.16/0.38  fof(t43_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,X3)<=>r1_tarski(X2,k3_subset_1(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 0.16/0.38  fof(idempotence_k8_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k8_subset_1(X1,X2,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k8_subset_1)).
% 0.16/0.38  fof(redefinition_k8_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k8_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_subset_1)).
% 0.16/0.38  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.16/0.38  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r2_hidden(X2,X1)=>(r2_hidden(X2,k8_setfam_1(X1,X3))<=>![X4]:(r2_hidden(X4,X3)=>r2_hidden(X2,X4)))))), inference(assume_negation,[status(cth)],[t58_setfam_1])).
% 0.16/0.38  fof(c_0_14, plain, ![X50, X51]:((r2_hidden(esk5_2(X50,X51),X50)|(X50=k1_xboole_0|r1_tarski(X51,k1_setfam_1(X50))))&(~r1_tarski(X51,esk5_2(X50,X51))|(X50=k1_xboole_0|r1_tarski(X51,k1_setfam_1(X50))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 0.16/0.38  fof(c_0_15, plain, ![X23, X24]:((~r1_tarski(k1_tarski(X23),X24)|r2_hidden(X23,X24))&(~r2_hidden(X23,X24)|r1_tarski(k1_tarski(X23),X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.16/0.38  fof(c_0_16, negated_conjecture, ![X57]:(m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0)))&(r2_hidden(esk7_0,esk6_0)&(((r2_hidden(esk9_0,esk8_0)|~r2_hidden(esk7_0,k8_setfam_1(esk6_0,esk8_0)))&(~r2_hidden(esk7_0,esk9_0)|~r2_hidden(esk7_0,k8_setfam_1(esk6_0,esk8_0))))&(r2_hidden(esk7_0,k8_setfam_1(esk6_0,esk8_0))|(~r2_hidden(X57,esk8_0)|r2_hidden(esk7_0,X57)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])])).
% 0.16/0.38  fof(c_0_17, plain, ![X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(k1_zfmisc_1(X41)))|k6_setfam_1(X41,X42)=k1_setfam_1(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).
% 0.16/0.38  cnf(c_0_18, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk5_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.16/0.38  cnf(c_0_19, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.16/0.38  cnf(c_0_20, negated_conjecture, (r2_hidden(esk7_0,k8_setfam_1(esk6_0,esk8_0))|r2_hidden(esk7_0,X1)|~r2_hidden(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.16/0.38  cnf(c_0_21, plain, (r2_hidden(esk5_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.16/0.38  fof(c_0_22, plain, ![X39, X40]:((X40=k1_xboole_0|k8_setfam_1(X39,X40)=k6_setfam_1(X39,X40)|~m1_subset_1(X40,k1_zfmisc_1(k1_zfmisc_1(X39))))&(X40!=k1_xboole_0|k8_setfam_1(X39,X40)=X39|~m1_subset_1(X40,k1_zfmisc_1(k1_zfmisc_1(X39))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).
% 0.16/0.38  cnf(c_0_23, plain, (k6_setfam_1(X2,X1)=k1_setfam_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.16/0.38  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.16/0.38  cnf(c_0_25, plain, (X1=k1_xboole_0|r1_tarski(k1_tarski(X2),k1_setfam_1(X1))|~r2_hidden(X2,esk5_2(X1,k1_tarski(X2)))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.16/0.38  cnf(c_0_26, negated_conjecture, (esk8_0=k1_xboole_0|r1_tarski(X1,k1_setfam_1(esk8_0))|r2_hidden(esk7_0,k8_setfam_1(esk6_0,esk8_0))|r2_hidden(esk7_0,esk5_2(esk8_0,X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.16/0.38  cnf(c_0_27, plain, (X1=k1_xboole_0|k8_setfam_1(X2,X1)=k6_setfam_1(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.16/0.38  cnf(c_0_28, negated_conjecture, (k6_setfam_1(esk6_0,esk8_0)=k1_setfam_1(esk8_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.16/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(esk9_0,esk8_0)|~r2_hidden(esk7_0,k8_setfam_1(esk6_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.16/0.38  cnf(c_0_30, negated_conjecture, (esk8_0=k1_xboole_0|r1_tarski(k1_tarski(esk7_0),k1_setfam_1(esk8_0))|r2_hidden(esk7_0,k8_setfam_1(esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.16/0.38  cnf(c_0_31, negated_conjecture, (k8_setfam_1(esk6_0,esk8_0)=k1_setfam_1(esk8_0)|esk8_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_24]), c_0_28])).
% 0.16/0.38  cnf(c_0_32, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.16/0.38  cnf(c_0_33, negated_conjecture, (esk8_0=k1_xboole_0|r1_tarski(k1_tarski(esk7_0),k1_setfam_1(esk8_0))|r2_hidden(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.16/0.38  cnf(c_0_34, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(esk9_0,esk8_0)|~r2_hidden(esk7_0,k1_setfam_1(esk8_0))), inference(spm,[status(thm)],[c_0_29, c_0_31])).
% 0.16/0.38  fof(c_0_35, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.16/0.38  fof(c_0_36, plain, ![X45, X46]:(~r2_hidden(X45,X46)|r1_tarski(k1_setfam_1(X46),X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.16/0.38  cnf(c_0_37, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(esk9_0,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.16/0.38  cnf(c_0_38, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.16/0.38  cnf(c_0_39, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.16/0.38  cnf(c_0_40, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(esk7_0,k8_setfam_1(esk6_0,esk8_0))|r2_hidden(esk7_0,esk9_0)), inference(spm,[status(thm)],[c_0_20, c_0_37])).
% 0.16/0.38  fof(c_0_41, plain, ![X43, X44]:((~m1_subset_1(X43,k1_zfmisc_1(X44))|r1_tarski(X43,X44))&(~r1_tarski(X43,X44)|m1_subset_1(X43,k1_zfmisc_1(X44)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.16/0.38  fof(c_0_42, plain, ![X38]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X38)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.16/0.38  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(X3))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.16/0.38  cnf(c_0_44, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(esk7_0,k1_setfam_1(esk8_0))|r2_hidden(esk7_0,esk9_0)), inference(spm,[status(thm)],[c_0_40, c_0_31])).
% 0.16/0.38  fof(c_0_45, plain, ![X35, X36, X37]:((~r1_xboole_0(X36,X37)|r1_tarski(X36,k3_subset_1(X35,X37))|~m1_subset_1(X37,k1_zfmisc_1(X35))|~m1_subset_1(X36,k1_zfmisc_1(X35)))&(~r1_tarski(X36,k3_subset_1(X35,X37))|r1_xboole_0(X36,X37)|~m1_subset_1(X37,k1_zfmisc_1(X35))|~m1_subset_1(X36,k1_zfmisc_1(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).
% 0.16/0.38  cnf(c_0_46, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.16/0.38  cnf(c_0_47, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.16/0.38  cnf(c_0_48, negated_conjecture, (~r2_hidden(esk7_0,esk9_0)|~r2_hidden(esk7_0,k8_setfam_1(esk6_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.16/0.38  cnf(c_0_49, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(esk7_0,esk9_0)|r2_hidden(esk7_0,X1)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.16/0.38  fof(c_0_50, plain, ![X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(X25))|k8_subset_1(X25,X26,X26)=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k8_subset_1])])])).
% 0.16/0.38  fof(c_0_51, plain, ![X27, X28, X29]:(~m1_subset_1(X28,k1_zfmisc_1(X27))|k8_subset_1(X27,X28,X29)=k3_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_subset_1])])).
% 0.16/0.38  cnf(c_0_52, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,k3_subset_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.16/0.38  cnf(c_0_53, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.16/0.38  cnf(c_0_54, negated_conjecture, (esk8_0=k1_xboole_0|r1_tarski(k1_tarski(esk7_0),k1_setfam_1(esk8_0))|~r2_hidden(esk7_0,esk9_0)), inference(spm,[status(thm)],[c_0_48, c_0_30])).
% 0.16/0.38  cnf(c_0_55, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(esk7_0,esk9_0)), inference(spm,[status(thm)],[c_0_49, c_0_37])).
% 0.16/0.38  cnf(c_0_56, plain, (k8_subset_1(X2,X1,X1)=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.16/0.38  cnf(c_0_57, plain, (k8_subset_1(X2,X1,X3)=k3_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.16/0.38  cnf(c_0_58, plain, (r1_xboole_0(k1_xboole_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_47])])).
% 0.16/0.38  cnf(c_0_59, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.16/0.38  cnf(c_0_60, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.16/0.38  cnf(c_0_61, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.16/0.38  cnf(c_0_62, negated_conjecture, (esk8_0=k1_xboole_0|r1_tarski(k1_tarski(esk7_0),k1_setfam_1(esk8_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.16/0.38  fof(c_0_63, plain, ![X15, X16, X18, X19, X20]:((r1_xboole_0(X15,X16)|r2_hidden(esk3_2(X15,X16),k3_xboole_0(X15,X16)))&(~r2_hidden(X20,k3_xboole_0(X18,X19))|~r1_xboole_0(X18,X19))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.16/0.38  cnf(c_0_64, plain, (k8_subset_1(X1,k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_47])).
% 0.16/0.38  cnf(c_0_65, plain, (k8_subset_1(X1,k1_xboole_0,X2)=k3_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_57, c_0_47])).
% 0.16/0.38  cnf(c_0_66, plain, (r1_xboole_0(k1_xboole_0,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.16/0.38  cnf(c_0_67, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.16/0.38  cnf(c_0_68, negated_conjecture, (esk8_0=k1_xboole_0|~r2_hidden(esk7_0,k1_setfam_1(esk8_0))|~r2_hidden(esk7_0,esk9_0)), inference(spm,[status(thm)],[c_0_48, c_0_31])).
% 0.16/0.38  cnf(c_0_69, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(esk7_0,k1_setfam_1(esk8_0))), inference(spm,[status(thm)],[c_0_32, c_0_62])).
% 0.16/0.38  cnf(c_0_70, plain, (k8_setfam_1(X2,X1)=X2|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.16/0.38  cnf(c_0_71, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.16/0.38  cnf(c_0_72, plain, (k3_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.16/0.38  cnf(c_0_73, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.16/0.38  cnf(c_0_74, negated_conjecture, (esk8_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_55])).
% 0.16/0.38  cnf(c_0_75, plain, (k8_setfam_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_70]), c_0_47])])).
% 0.16/0.38  cnf(c_0_76, negated_conjecture, (r2_hidden(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.16/0.38  cnf(c_0_77, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])])).
% 0.16/0.38  cnf(c_0_78, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_74]), c_0_74]), c_0_75]), c_0_76])]), c_0_77]), ['proof']).
% 0.16/0.38  # SZS output end CNFRefutation
% 0.16/0.38  # Proof object total steps             : 79
% 0.16/0.38  # Proof object clause steps            : 52
% 0.16/0.38  # Proof object formula steps           : 27
% 0.16/0.38  # Proof object conjectures             : 25
% 0.16/0.38  # Proof object clause conjectures      : 22
% 0.16/0.38  # Proof object formula conjectures     : 3
% 0.16/0.38  # Proof object initial clauses used    : 23
% 0.16/0.38  # Proof object initial formulas used   : 13
% 0.16/0.38  # Proof object generating inferences   : 26
% 0.16/0.38  # Proof object simplifying inferences  : 17
% 0.16/0.38  # Training examples: 0 positive, 0 negative
% 0.16/0.38  # Parsed axioms                        : 18
% 0.16/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.38  # Initial clauses                      : 33
% 0.16/0.38  # Removed in clause preprocessing      : 0
% 0.16/0.38  # Initial clauses in saturation        : 33
% 0.16/0.38  # Processed clauses                    : 520
% 0.16/0.38  # ...of these trivial                  : 5
% 0.16/0.38  # ...subsumed                          : 210
% 0.16/0.38  # ...remaining for further processing  : 305
% 0.16/0.38  # Other redundant clauses eliminated   : 2
% 0.16/0.38  # Clauses deleted for lack of memory   : 0
% 0.16/0.38  # Backward-subsumed                    : 37
% 0.16/0.38  # Backward-rewritten                   : 138
% 0.16/0.38  # Generated clauses                    : 973
% 0.16/0.38  # ...of the previous two non-trivial   : 940
% 0.16/0.38  # Contextual simplify-reflections      : 11
% 0.16/0.38  # Paramodulations                      : 971
% 0.16/0.38  # Factorizations                       : 0
% 0.16/0.38  # Equation resolutions                 : 2
% 0.16/0.38  # Propositional unsat checks           : 0
% 0.16/0.38  #    Propositional check models        : 0
% 0.16/0.38  #    Propositional check unsatisfiable : 0
% 0.16/0.38  #    Propositional clauses             : 0
% 0.16/0.38  #    Propositional clauses after purity: 0
% 0.16/0.38  #    Propositional unsat core size     : 0
% 0.16/0.38  #    Propositional preprocessing time  : 0.000
% 0.16/0.38  #    Propositional encoding time       : 0.000
% 0.16/0.38  #    Propositional solver time         : 0.000
% 0.16/0.38  #    Success case prop preproc time    : 0.000
% 0.16/0.38  #    Success case prop encoding time   : 0.000
% 0.16/0.38  #    Success case prop solver time     : 0.000
% 0.16/0.38  # Current number of processed clauses  : 96
% 0.16/0.38  #    Positive orientable unit clauses  : 14
% 0.16/0.38  #    Positive unorientable unit clauses: 0
% 0.16/0.38  #    Negative unit clauses             : 4
% 0.16/0.38  #    Non-unit-clauses                  : 78
% 0.16/0.38  # Current number of unprocessed clauses: 404
% 0.16/0.38  # ...number of literals in the above   : 1336
% 0.16/0.38  # Current number of archived formulas  : 0
% 0.16/0.38  # Current number of archived clauses   : 207
% 0.16/0.38  # Clause-clause subsumption calls (NU) : 5302
% 0.16/0.38  # Rec. Clause-clause subsumption calls : 4190
% 0.16/0.38  # Non-unit clause-clause subsumptions  : 168
% 0.16/0.38  # Unit Clause-clause subsumption calls : 185
% 0.16/0.38  # Rewrite failures with RHS unbound    : 0
% 0.16/0.38  # BW rewrite match attempts            : 16
% 0.16/0.38  # BW rewrite match successes           : 10
% 0.16/0.38  # Condensation attempts                : 0
% 0.16/0.38  # Condensation successes               : 0
% 0.16/0.38  # Termbank termtop insertions          : 15140
% 0.16/0.38  
% 0.16/0.38  # -------------------------------------------------
% 0.16/0.38  # User time                : 0.060 s
% 0.16/0.38  # System time              : 0.010 s
% 0.16/0.38  # Total time               : 0.070 s
% 0.16/0.38  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
