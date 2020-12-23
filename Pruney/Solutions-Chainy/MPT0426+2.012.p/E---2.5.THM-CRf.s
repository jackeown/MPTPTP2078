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
% DateTime   : Thu Dec  3 10:47:48 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   92 (2055 expanded)
%              Number of clauses        :   63 ( 911 expanded)
%              Number of leaves         :   14 ( 497 expanded)
%              Depth                    :   27
%              Number of atoms          :  258 (7384 expanded)
%              Number of equality atoms :   66 (1393 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(t58_setfam_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( r2_hidden(X2,X1)
       => ( r2_hidden(X2,k8_setfam_1(X1,X3))
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
             => r2_hidden(X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(l35_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(dt_o_2_1_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(o_2_1_setfam_1(X1,X2),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_2_1_setfam_1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_14,plain,(
    ! [X24,X25] :
      ( ( ~ r1_tarski(k1_tarski(X24),X25)
        | r2_hidden(X24,X25) )
      & ( ~ r2_hidden(X24,X25)
        | r1_tarski(k1_tarski(X24),X25) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).

fof(c_0_15,plain,(
    ! [X43,X44] :
      ( ( r2_hidden(esk4_2(X43,X44),X43)
        | X43 = k1_xboole_0
        | r1_tarski(X44,k1_setfam_1(X43)) )
      & ( ~ r1_tarski(X44,esk4_2(X43,X44))
        | X43 = k1_xboole_0
        | r1_tarski(X44,k1_setfam_1(X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( r2_hidden(X2,X1)
         => ( r2_hidden(X2,k8_setfam_1(X1,X3))
          <=> ! [X4] :
                ( r2_hidden(X4,X3)
               => r2_hidden(X2,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t58_setfam_1])).

fof(c_0_17,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X32,X33] :
      ( ( X33 = k1_xboole_0
        | k8_setfam_1(X32,X33) = k6_setfam_1(X32,X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k1_zfmisc_1(X32))) )
      & ( X33 != k1_xboole_0
        | k8_setfam_1(X32,X33) = X32
        | ~ m1_subset_1(X33,k1_zfmisc_1(k1_zfmisc_1(X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

fof(c_0_21,negated_conjecture,(
    ! [X50] :
      ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk5_0)))
      & r2_hidden(esk6_0,esk5_0)
      & ( r2_hidden(esk8_0,esk7_0)
        | ~ r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0)) )
      & ( ~ r2_hidden(esk6_0,esk8_0)
        | ~ r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0)) )
      & ( r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))
        | ~ r2_hidden(X50,esk7_0)
        | r2_hidden(esk6_0,X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])])])).

cnf(c_0_22,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_2(X1,k1_tarski(X2)),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k1_zfmisc_1(X36)))
      | k6_setfam_1(X36,X37) = k1_setfam_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_setfam_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k6_setfam_1(esk5_0,esk7_0) = k8_setfam_1(esk5_0,esk7_0)
    | k1_xboole_0 = esk7_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_31,plain,(
    ! [X26,X27,X28] :
      ( ( r2_hidden(X26,X27)
        | ~ r2_hidden(X26,k4_xboole_0(X27,k1_tarski(X28))) )
      & ( X26 != X28
        | ~ r2_hidden(X26,k4_xboole_0(X27,k1_tarski(X28))) )
      & ( ~ r2_hidden(X26,X27)
        | X26 = X28
        | r2_hidden(X26,k4_xboole_0(X27,k1_tarski(X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_32,plain,(
    ! [X31] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X31)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k1_setfam_1(esk7_0) = k8_setfam_1(esk5_0,esk7_0)
    | k1_xboole_0 = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_26])])).

cnf(c_0_35,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_36,plain,(
    ! [X22,X23] :
      ( ( k4_xboole_0(k1_tarski(X22),X23) != k1_xboole_0
        | r2_hidden(X22,X23) )
      & ( ~ r2_hidden(X22,X23)
        | k4_xboole_0(k1_tarski(X22),X23) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).

fof(c_0_37,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X17,X16)
        | X17 = X15
        | X16 != k1_tarski(X15) )
      & ( X18 != X15
        | r2_hidden(X18,X16)
        | X16 != k1_tarski(X15) )
      & ( ~ r2_hidden(esk3_2(X19,X20),X20)
        | esk3_2(X19,X20) != X19
        | X20 = k1_tarski(X19) )
      & ( r2_hidden(esk3_2(X19,X20),X20)
        | esk3_2(X19,X20) = X19
        | X20 = k1_tarski(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_38,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0)
    | ~ r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( k1_xboole_0 = esk7_0
    | r2_hidden(X1,k8_setfam_1(esk5_0,esk7_0))
    | r2_hidden(esk1_1(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_42,plain,(
    ! [X29,X30] :
      ( ( ~ m1_subset_1(X30,X29)
        | r2_hidden(X30,X29)
        | v1_xboole_0(X29) )
      & ( ~ r2_hidden(X30,X29)
        | m1_subset_1(X30,X29)
        | v1_xboole_0(X29) )
      & ( ~ m1_subset_1(X30,X29)
        | v1_xboole_0(X30)
        | ~ v1_xboole_0(X29) )
      & ( ~ v1_xboole_0(X30)
        | m1_subset_1(X30,X29)
        | ~ v1_xboole_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_43,plain,(
    ! [X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(X34)))
      | m1_subset_1(o_2_1_setfam_1(X34,X35),X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_o_2_1_setfam_1])])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X1))) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( k8_setfam_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_39])])).

cnf(c_0_48,negated_conjecture,
    ( k1_xboole_0 = esk7_0
    | r2_hidden(esk1_1(esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( m1_subset_1(o_2_1_setfam_1(X2,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,k1_tarski(X2))
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).

cnf(c_0_53,negated_conjecture,
    ( k8_setfam_1(X1,esk7_0) = X1
    | r2_hidden(esk1_1(esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_55,plain,
    ( r2_hidden(o_2_1_setfam_1(X1,X2),X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( k1_xboole_0 = esk7_0
    | r2_hidden(esk4_2(esk7_0,k1_tarski(X1)),esk7_0)
    | r2_hidden(X1,k8_setfam_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_34])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_1(esk7_0),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_53]),c_0_54])])).

cnf(c_0_59,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_39]),c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( k1_xboole_0 = esk7_0
    | r2_hidden(esk4_2(esk7_0,k1_tarski(esk6_0)),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_58]),c_0_22])).

cnf(c_0_62,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk4_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_63,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))
    | r2_hidden(esk6_0,X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_tarski(esk6_0)),esk7_0)
    | r2_hidden(esk8_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_tarski(X2),k1_setfam_1(X1))
    | ~ r2_hidden(X2,esk4_2(X1,k1_tarski(X2))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_2(esk7_0,k1_tarski(esk6_0)))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_40])).

cnf(c_0_68,negated_conjecture,
    ( k1_xboole_0 = esk7_0
    | r1_tarski(k1_tarski(esk6_0),k1_setfam_1(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

fof(c_0_69,plain,(
    ! [X38,X39] :
      ( ~ r2_hidden(X38,X39)
      | r1_tarski(k1_setfam_1(X39),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_70,negated_conjecture,
    ( k1_xboole_0 = esk7_0
    | r2_hidden(esk6_0,k1_setfam_1(esk7_0))
    | r2_hidden(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_68])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( k1_xboole_0 = esk7_0
    | r2_hidden(esk8_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_34]),c_0_40])).

fof(c_0_73,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_74,negated_conjecture,
    ( k1_xboole_0 = esk7_0
    | r1_tarski(k8_setfam_1(esk5_0,esk7_0),X1)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_34])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_72]),c_0_61])).

cnf(c_0_76,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( k1_xboole_0 = esk7_0
    | r1_tarski(k8_setfam_1(esk5_0,esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( k1_xboole_0 = esk7_0
    | r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,k8_setfam_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))
    | r2_hidden(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( ~ r2_hidden(esk6_0,esk8_0)
    | ~ r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_81,negated_conjecture,
    ( k1_xboole_0 = esk7_0
    | r2_hidden(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( k1_xboole_0 = esk7_0
    | r2_hidden(esk4_2(esk7_0,k1_tarski(esk6_0)),esk7_0)
    | ~ r2_hidden(esk6_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_57])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_81]),c_0_61])).

cnf(c_0_84,negated_conjecture,
    ( k1_xboole_0 = esk7_0
    | r2_hidden(esk4_2(esk7_0,k1_tarski(esk6_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83])])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_tarski(esk6_0)),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_84]),c_0_61])).

cnf(c_0_86,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_83])])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_2(esk7_0,k1_tarski(esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_85]),c_0_86])).

cnf(c_0_88,negated_conjecture,
    ( k1_xboole_0 = esk7_0
    | r1_tarski(k1_tarski(esk6_0),k1_setfam_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_87])).

cnf(c_0_89,negated_conjecture,
    ( k1_xboole_0 = esk7_0
    | r2_hidden(esk6_0,k1_setfam_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_88])).

cnf(c_0_90,negated_conjecture,
    ( k1_xboole_0 = esk7_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_34]),c_0_86])).

cnf(c_0_91,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_90]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:33:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 3.03/3.21  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 3.03/3.21  # and selection function SelectComplexExceptUniqMaxHorn.
% 3.03/3.21  #
% 3.03/3.21  # Preprocessing time       : 0.040 s
% 3.03/3.21  # Presaturation interreduction done
% 3.03/3.21  
% 3.03/3.21  # Proof found!
% 3.03/3.21  # SZS status Theorem
% 3.03/3.21  # SZS output start CNFRefutation
% 3.03/3.21  fof(t37_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 3.03/3.21  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 3.03/3.21  fof(t58_setfam_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r2_hidden(X2,X1)=>(r2_hidden(X2,k8_setfam_1(X1,X3))<=>![X4]:(r2_hidden(X4,X3)=>r2_hidden(X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_setfam_1)).
% 3.03/3.21  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.03/3.21  fof(d10_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((X2!=k1_xboole_0=>k8_setfam_1(X1,X2)=k6_setfam_1(X1,X2))&(X2=k1_xboole_0=>k8_setfam_1(X1,X2)=X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.03/3.21  fof(redefinition_k6_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k6_setfam_1(X1,X2)=k1_setfam_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.03/3.21  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.03/3.21  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.03/3.21  fof(l35_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 3.03/3.21  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.03/3.21  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.03/3.21  fof(dt_o_2_1_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(o_2_1_setfam_1(X1,X2),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_2_1_setfam_1)).
% 3.03/3.21  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 3.03/3.21  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.03/3.21  fof(c_0_14, plain, ![X24, X25]:((~r1_tarski(k1_tarski(X24),X25)|r2_hidden(X24,X25))&(~r2_hidden(X24,X25)|r1_tarski(k1_tarski(X24),X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).
% 3.03/3.21  fof(c_0_15, plain, ![X43, X44]:((r2_hidden(esk4_2(X43,X44),X43)|(X43=k1_xboole_0|r1_tarski(X44,k1_setfam_1(X43))))&(~r1_tarski(X44,esk4_2(X43,X44))|(X43=k1_xboole_0|r1_tarski(X44,k1_setfam_1(X43))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 3.03/3.21  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r2_hidden(X2,X1)=>(r2_hidden(X2,k8_setfam_1(X1,X3))<=>![X4]:(r2_hidden(X4,X3)=>r2_hidden(X2,X4)))))), inference(assume_negation,[status(cth)],[t58_setfam_1])).
% 3.03/3.21  fof(c_0_17, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 3.03/3.21  cnf(c_0_18, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.03/3.21  cnf(c_0_19, plain, (r2_hidden(esk4_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.03/3.21  fof(c_0_20, plain, ![X32, X33]:((X33=k1_xboole_0|k8_setfam_1(X32,X33)=k6_setfam_1(X32,X33)|~m1_subset_1(X33,k1_zfmisc_1(k1_zfmisc_1(X32))))&(X33!=k1_xboole_0|k8_setfam_1(X32,X33)=X32|~m1_subset_1(X33,k1_zfmisc_1(k1_zfmisc_1(X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).
% 3.03/3.21  fof(c_0_21, negated_conjecture, ![X50]:(m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk5_0)))&(r2_hidden(esk6_0,esk5_0)&(((r2_hidden(esk8_0,esk7_0)|~r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0)))&(~r2_hidden(esk6_0,esk8_0)|~r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))))&(r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))|(~r2_hidden(X50,esk7_0)|r2_hidden(esk6_0,X50)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])])])).
% 3.03/3.21  cnf(c_0_22, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.03/3.21  cnf(c_0_23, plain, (X1=k1_xboole_0|r2_hidden(esk4_2(X1,k1_tarski(X2)),X1)|r2_hidden(X2,k1_setfam_1(X1))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 3.03/3.21  fof(c_0_24, plain, ![X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k1_zfmisc_1(X36)))|k6_setfam_1(X36,X37)=k1_setfam_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).
% 3.03/3.21  cnf(c_0_25, plain, (X1=k1_xboole_0|k8_setfam_1(X2,X1)=k6_setfam_1(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.03/3.21  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.03/3.21  cnf(c_0_27, plain, (X1=k1_xboole_0|r2_hidden(X2,k1_setfam_1(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 3.03/3.21  cnf(c_0_28, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.03/3.21  cnf(c_0_29, plain, (k6_setfam_1(X2,X1)=k1_setfam_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 3.03/3.21  cnf(c_0_30, negated_conjecture, (k6_setfam_1(esk5_0,esk7_0)=k8_setfam_1(esk5_0,esk7_0)|k1_xboole_0=esk7_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 3.03/3.21  fof(c_0_31, plain, ![X26, X27, X28]:(((r2_hidden(X26,X27)|~r2_hidden(X26,k4_xboole_0(X27,k1_tarski(X28))))&(X26!=X28|~r2_hidden(X26,k4_xboole_0(X27,k1_tarski(X28)))))&(~r2_hidden(X26,X27)|X26=X28|r2_hidden(X26,k4_xboole_0(X27,k1_tarski(X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 3.03/3.21  fof(c_0_32, plain, ![X31]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X31)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 3.03/3.21  cnf(c_0_33, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)|r2_hidden(X2,k1_setfam_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 3.03/3.21  cnf(c_0_34, negated_conjecture, (k1_setfam_1(esk7_0)=k8_setfam_1(esk5_0,esk7_0)|k1_xboole_0=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_26])])).
% 3.03/3.21  cnf(c_0_35, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.03/3.21  fof(c_0_36, plain, ![X22, X23]:((k4_xboole_0(k1_tarski(X22),X23)!=k1_xboole_0|r2_hidden(X22,X23))&(~r2_hidden(X22,X23)|k4_xboole_0(k1_tarski(X22),X23)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).
% 3.03/3.21  fof(c_0_37, plain, ![X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X17,X16)|X17=X15|X16!=k1_tarski(X15))&(X18!=X15|r2_hidden(X18,X16)|X16!=k1_tarski(X15)))&((~r2_hidden(esk3_2(X19,X20),X20)|esk3_2(X19,X20)!=X19|X20=k1_tarski(X19))&(r2_hidden(esk3_2(X19,X20),X20)|esk3_2(X19,X20)=X19|X20=k1_tarski(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 3.03/3.21  cnf(c_0_38, plain, (k8_setfam_1(X2,X1)=X2|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.03/3.21  cnf(c_0_39, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.03/3.21  cnf(c_0_40, negated_conjecture, (r2_hidden(esk8_0,esk7_0)|~r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.03/3.21  cnf(c_0_41, negated_conjecture, (k1_xboole_0=esk7_0|r2_hidden(X1,k8_setfam_1(esk5_0,esk7_0))|r2_hidden(esk1_1(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 3.03/3.21  fof(c_0_42, plain, ![X29, X30]:(((~m1_subset_1(X30,X29)|r2_hidden(X30,X29)|v1_xboole_0(X29))&(~r2_hidden(X30,X29)|m1_subset_1(X30,X29)|v1_xboole_0(X29)))&((~m1_subset_1(X30,X29)|v1_xboole_0(X30)|~v1_xboole_0(X29))&(~v1_xboole_0(X30)|m1_subset_1(X30,X29)|~v1_xboole_0(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 3.03/3.21  fof(c_0_43, plain, ![X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(X34)))|m1_subset_1(o_2_1_setfam_1(X34,X35),X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_o_2_1_setfam_1])])).
% 3.03/3.21  cnf(c_0_44, plain, (~r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X1)))), inference(er,[status(thm)],[c_0_35])).
% 3.03/3.21  cnf(c_0_45, plain, (k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.03/3.21  cnf(c_0_46, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 3.03/3.21  cnf(c_0_47, plain, (k8_setfam_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_38]), c_0_39])])).
% 3.03/3.21  cnf(c_0_48, negated_conjecture, (k1_xboole_0=esk7_0|r2_hidden(esk1_1(esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 3.03/3.21  cnf(c_0_49, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.03/3.21  cnf(c_0_50, plain, (m1_subset_1(o_2_1_setfam_1(X2,X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.03/3.21  cnf(c_0_51, plain, (~r2_hidden(X1,k1_tarski(X2))|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 3.03/3.21  cnf(c_0_52, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).
% 3.03/3.21  cnf(c_0_53, negated_conjecture, (k8_setfam_1(X1,esk7_0)=X1|r2_hidden(esk1_1(esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 3.03/3.21  cnf(c_0_54, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.03/3.21  cnf(c_0_55, plain, (r2_hidden(o_2_1_setfam_1(X1,X2),X2)|v1_xboole_0(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 3.03/3.21  cnf(c_0_56, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 3.03/3.21  cnf(c_0_57, negated_conjecture, (k1_xboole_0=esk7_0|r2_hidden(esk4_2(esk7_0,k1_tarski(X1)),esk7_0)|r2_hidden(X1,k8_setfam_1(esk5_0,esk7_0))), inference(spm,[status(thm)],[c_0_23, c_0_34])).
% 3.03/3.21  cnf(c_0_58, negated_conjecture, (r2_hidden(esk1_1(esk7_0),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_53]), c_0_54])])).
% 3.03/3.21  cnf(c_0_59, plain, (v1_xboole_0(k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_39]), c_0_56])).
% 3.03/3.21  cnf(c_0_60, negated_conjecture, (k1_xboole_0=esk7_0|r2_hidden(esk4_2(esk7_0,k1_tarski(esk6_0)),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_40, c_0_57])).
% 3.03/3.21  cnf(c_0_61, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_58]), c_0_22])).
% 3.03/3.21  cnf(c_0_62, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk4_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.03/3.21  cnf(c_0_63, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.03/3.21  cnf(c_0_64, negated_conjecture, (r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))|r2_hidden(esk6_0,X1)|~r2_hidden(X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.03/3.21  cnf(c_0_65, negated_conjecture, (r2_hidden(esk4_2(esk7_0,k1_tarski(esk6_0)),esk7_0)|r2_hidden(esk8_0,esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 3.03/3.21  cnf(c_0_66, plain, (X1=k1_xboole_0|r1_tarski(k1_tarski(X2),k1_setfam_1(X1))|~r2_hidden(X2,esk4_2(X1,k1_tarski(X2)))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 3.03/3.21  cnf(c_0_67, negated_conjecture, (r2_hidden(esk6_0,esk4_2(esk7_0,k1_tarski(esk6_0)))|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_40])).
% 3.03/3.21  cnf(c_0_68, negated_conjecture, (k1_xboole_0=esk7_0|r1_tarski(k1_tarski(esk6_0),k1_setfam_1(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 3.03/3.21  fof(c_0_69, plain, ![X38, X39]:(~r2_hidden(X38,X39)|r1_tarski(k1_setfam_1(X39),X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 3.03/3.21  cnf(c_0_70, negated_conjecture, (k1_xboole_0=esk7_0|r2_hidden(esk6_0,k1_setfam_1(esk7_0))|r2_hidden(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_18, c_0_68])).
% 3.03/3.21  cnf(c_0_71, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 3.03/3.21  cnf(c_0_72, negated_conjecture, (k1_xboole_0=esk7_0|r2_hidden(esk8_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_34]), c_0_40])).
% 3.03/3.21  fof(c_0_73, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 3.03/3.21  cnf(c_0_74, negated_conjecture, (k1_xboole_0=esk7_0|r1_tarski(k8_setfam_1(esk5_0,esk7_0),X1)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_71, c_0_34])).
% 3.03/3.21  cnf(c_0_75, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_72]), c_0_61])).
% 3.03/3.21  cnf(c_0_76, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 3.03/3.21  cnf(c_0_77, negated_conjecture, (k1_xboole_0=esk7_0|r1_tarski(k8_setfam_1(esk5_0,esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 3.03/3.21  cnf(c_0_78, negated_conjecture, (k1_xboole_0=esk7_0|r2_hidden(X1,esk8_0)|~r2_hidden(X1,k8_setfam_1(esk5_0,esk7_0))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 3.03/3.21  cnf(c_0_79, negated_conjecture, (r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))|r2_hidden(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_64, c_0_75])).
% 3.03/3.21  cnf(c_0_80, negated_conjecture, (~r2_hidden(esk6_0,esk8_0)|~r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.03/3.21  cnf(c_0_81, negated_conjecture, (k1_xboole_0=esk7_0|r2_hidden(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 3.03/3.21  cnf(c_0_82, negated_conjecture, (k1_xboole_0=esk7_0|r2_hidden(esk4_2(esk7_0,k1_tarski(esk6_0)),esk7_0)|~r2_hidden(esk6_0,esk8_0)), inference(spm,[status(thm)],[c_0_80, c_0_57])).
% 3.03/3.21  cnf(c_0_83, negated_conjecture, (r2_hidden(esk6_0,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_81]), c_0_61])).
% 3.03/3.21  cnf(c_0_84, negated_conjecture, (k1_xboole_0=esk7_0|r2_hidden(esk4_2(esk7_0,k1_tarski(esk6_0)),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83])])).
% 3.03/3.21  cnf(c_0_85, negated_conjecture, (r2_hidden(esk4_2(esk7_0,k1_tarski(esk6_0)),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_84]), c_0_61])).
% 3.03/3.21  cnf(c_0_86, negated_conjecture, (~r2_hidden(esk6_0,k8_setfam_1(esk5_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_83])])).
% 3.03/3.21  cnf(c_0_87, negated_conjecture, (r2_hidden(esk6_0,esk4_2(esk7_0,k1_tarski(esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_85]), c_0_86])).
% 3.03/3.21  cnf(c_0_88, negated_conjecture, (k1_xboole_0=esk7_0|r1_tarski(k1_tarski(esk6_0),k1_setfam_1(esk7_0))), inference(spm,[status(thm)],[c_0_66, c_0_87])).
% 3.03/3.21  cnf(c_0_89, negated_conjecture, (k1_xboole_0=esk7_0|r2_hidden(esk6_0,k1_setfam_1(esk7_0))), inference(spm,[status(thm)],[c_0_18, c_0_88])).
% 3.03/3.21  cnf(c_0_90, negated_conjecture, (k1_xboole_0=esk7_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_34]), c_0_86])).
% 3.03/3.21  cnf(c_0_91, plain, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_90]), c_0_61]), ['proof']).
% 3.03/3.21  # SZS output end CNFRefutation
% 3.03/3.21  # Proof object total steps             : 92
% 3.03/3.21  # Proof object clause steps            : 63
% 3.03/3.21  # Proof object formula steps           : 29
% 3.03/3.21  # Proof object conjectures             : 37
% 3.03/3.21  # Proof object clause conjectures      : 34
% 3.03/3.21  # Proof object formula conjectures     : 3
% 3.03/3.21  # Proof object initial clauses used    : 22
% 3.03/3.21  # Proof object initial formulas used   : 14
% 3.03/3.21  # Proof object generating inferences   : 35
% 3.03/3.21  # Proof object simplifying inferences  : 26
% 3.03/3.21  # Training examples: 0 positive, 0 negative
% 3.03/3.21  # Parsed axioms                        : 15
% 3.03/3.21  # Removed by relevancy pruning/SinE    : 0
% 3.03/3.21  # Initial clauses                      : 34
% 3.03/3.21  # Removed in clause preprocessing      : 0
% 3.03/3.21  # Initial clauses in saturation        : 34
% 3.03/3.21  # Processed clauses                    : 5302
% 3.03/3.21  # ...of these trivial                  : 316
% 3.03/3.21  # ...subsumed                          : 2055
% 3.03/3.21  # ...remaining for further processing  : 2931
% 3.03/3.21  # Other redundant clauses eliminated   : 388
% 3.03/3.21  # Clauses deleted for lack of memory   : 0
% 3.03/3.21  # Backward-subsumed                    : 613
% 3.03/3.21  # Backward-rewritten                   : 987
% 3.03/3.21  # Generated clauses                    : 313789
% 3.03/3.21  # ...of the previous two non-trivial   : 293587
% 3.03/3.21  # Contextual simplify-reflections      : 32
% 3.03/3.21  # Paramodulations                      : 313267
% 3.03/3.21  # Factorizations                       : 65
% 3.03/3.21  # Equation resolutions                 : 388
% 3.03/3.21  # Propositional unsat checks           : 0
% 3.03/3.21  #    Propositional check models        : 0
% 3.03/3.21  #    Propositional check unsatisfiable : 0
% 3.03/3.21  #    Propositional clauses             : 0
% 3.03/3.21  #    Propositional clauses after purity: 0
% 3.03/3.21  #    Propositional unsat core size     : 0
% 3.03/3.21  #    Propositional preprocessing time  : 0.000
% 3.03/3.21  #    Propositional encoding time       : 0.000
% 3.03/3.21  #    Propositional solver time         : 0.000
% 3.03/3.21  #    Success case prop preproc time    : 0.000
% 3.03/3.21  #    Success case prop encoding time   : 0.000
% 3.03/3.21  #    Success case prop solver time     : 0.000
% 3.03/3.21  # Current number of processed clauses  : 1223
% 3.03/3.21  #    Positive orientable unit clauses  : 70
% 3.03/3.21  #    Positive unorientable unit clauses: 0
% 3.03/3.21  #    Negative unit clauses             : 16
% 3.03/3.21  #    Non-unit-clauses                  : 1137
% 3.03/3.21  # Current number of unprocessed clauses: 284309
% 3.03/3.21  # ...number of literals in the above   : 1498177
% 3.03/3.21  # Current number of archived formulas  : 0
% 3.03/3.21  # Current number of archived clauses   : 1704
% 3.03/3.21  # Clause-clause subsumption calls (NU) : 292649
% 3.03/3.21  # Rec. Clause-clause subsumption calls : 130758
% 3.03/3.21  # Non-unit clause-clause subsumptions  : 1673
% 3.03/3.21  # Unit Clause-clause subsumption calls : 12269
% 3.03/3.21  # Rewrite failures with RHS unbound    : 0
% 3.03/3.21  # BW rewrite match attempts            : 238
% 3.03/3.21  # BW rewrite match successes           : 58
% 3.03/3.21  # Condensation attempts                : 0
% 3.03/3.21  # Condensation successes               : 0
% 3.03/3.21  # Termbank termtop insertions          : 6108375
% 3.03/3.22  
% 3.03/3.22  # -------------------------------------------------
% 3.03/3.22  # User time                : 2.749 s
% 3.03/3.22  # System time              : 0.132 s
% 3.03/3.22  # Total time               : 2.882 s
% 3.03/3.22  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
