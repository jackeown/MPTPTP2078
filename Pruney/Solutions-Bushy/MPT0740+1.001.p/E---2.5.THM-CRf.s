%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0740+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:07 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 511 expanded)
%              Number of clauses        :   53 ( 252 expanded)
%              Number of leaves         :   13 ( 121 expanded)
%              Depth                    :   16
%              Number of atoms          :  242 (1982 expanded)
%              Number of equality atoms :   20 ( 230 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(t30_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(d4_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
    <=> ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_ordinal1)).

fof(d3_ordinal1,axiom,(
    ! [X1] :
      ( v2_ordinal1(X1)
    <=> ! [X2,X3] :
          ~ ( r2_hidden(X2,X1)
            & r2_hidden(X3,X1)
            & ~ r2_hidden(X2,X3)
            & X2 != X3
            & ~ r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(t92_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(c_0_13,plain,(
    ! [X36,X37,X38] :
      ( ~ r2_hidden(X36,X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X38))
      | m1_subset_1(X36,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_14,plain,(
    ! [X34,X35] :
      ( ( ~ m1_subset_1(X34,k1_zfmisc_1(X35))
        | r1_tarski(X34,X35) )
      & ( ~ r1_tarski(X34,X35)
        | m1_subset_1(X34,k1_zfmisc_1(X35)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_ordinal1(X6)
        | ~ r2_hidden(X7,X6)
        | r1_tarski(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_ordinal1(X8) )
      & ( ~ r1_tarski(esk1_1(X8),X8)
        | v1_ordinal1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

fof(c_0_18,plain,(
    ! [X17,X18,X19,X21,X22,X23,X24,X26] :
      ( ( r2_hidden(X19,esk4_3(X17,X18,X19))
        | ~ r2_hidden(X19,X18)
        | X18 != k3_tarski(X17) )
      & ( r2_hidden(esk4_3(X17,X18,X19),X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k3_tarski(X17) )
      & ( ~ r2_hidden(X21,X22)
        | ~ r2_hidden(X22,X17)
        | r2_hidden(X21,X18)
        | X18 != k3_tarski(X17) )
      & ( ~ r2_hidden(esk5_2(X23,X24),X24)
        | ~ r2_hidden(esk5_2(X23,X24),X26)
        | ~ r2_hidden(X26,X23)
        | X24 = k3_tarski(X23) )
      & ( r2_hidden(esk5_2(X23,X24),esk6_2(X23,X24))
        | r2_hidden(esk5_2(X23,X24),X24)
        | X24 = k3_tarski(X23) )
      & ( r2_hidden(esk6_2(X23,X24),X23)
        | r2_hidden(esk5_2(X23,X24),X24)
        | X24 = k3_tarski(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,esk4_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => v3_ordinal1(k3_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t30_ordinal1])).

fof(c_0_23,plain,(
    ! [X39,X40] :
      ( ~ r2_hidden(X39,X40)
      | ~ v1_xboole_0(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_24,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ v1_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,esk4_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_21])).

fof(c_0_27,negated_conjecture,
    ( v3_ordinal1(esk7_0)
    & ~ v3_ordinal1(k3_tarski(esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_28,plain,(
    ! [X16] :
      ( ( v1_ordinal1(X16)
        | ~ v3_ordinal1(X16) )
      & ( v2_ordinal1(X16)
        | ~ v3_ordinal1(X16) )
      & ( ~ v1_ordinal1(X16)
        | ~ v2_ordinal1(X16)
        | v3_ordinal1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_ordinal1])])])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(esk4_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X10,X11,X12,X13] :
      ( ( ~ v2_ordinal1(X10)
        | ~ r2_hidden(X11,X10)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X11,X12)
        | X11 = X12
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_1(X13),X13)
        | v2_ordinal1(X13) )
      & ( r2_hidden(esk3_1(X13),X13)
        | v2_ordinal1(X13) )
      & ( ~ r2_hidden(esk2_1(X13),esk3_1(X13))
        | v2_ordinal1(X13) )
      & ( esk2_1(X13) != esk3_1(X13)
        | v2_ordinal1(X13) )
      & ( ~ r2_hidden(esk3_1(X13),esk2_1(X13))
        | v2_ordinal1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_ordinal1])])])])])])])).

fof(c_0_32,plain,(
    ! [X28,X29] :
      ( ~ v3_ordinal1(X29)
      | ~ r2_hidden(X28,X29)
      | v3_ordinal1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(esk4_3(X3,k3_tarski(X3),X1),X2)
    | ~ r2_hidden(X1,k3_tarski(X3))
    | ~ v1_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_34,plain,(
    ! [X5] :
      ( ( v1_ordinal1(X5)
        | ~ v3_ordinal1(X5) )
      & ( v2_ordinal1(X5)
        | ~ v3_ordinal1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

cnf(c_0_35,negated_conjecture,
    ( ~ v3_ordinal1(k3_tarski(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( v3_ordinal1(X1)
    | ~ v1_ordinal1(X1)
    | ~ v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k3_tarski(X2))
    | ~ v1_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_30])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_42,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( v3_ordinal1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_ordinal1(k3_tarski(esk7_0))
    | ~ v1_ordinal1(k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,plain,
    ( v2_ordinal1(k3_tarski(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_46,plain,(
    ! [X41,X42] :
      ( ~ r2_hidden(X41,X42)
      | r1_tarski(X41,k3_tarski(X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_zfmisc_1])])).

cnf(c_0_47,plain,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k3_tarski(X2))
    | ~ v3_ordinal1(esk4_3(X2,k3_tarski(X2),X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_26])).

cnf(c_0_48,plain,
    ( v3_ordinal1(esk4_3(X1,k3_tarski(X1),X2))
    | ~ r2_hidden(X2,k3_tarski(X1))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_30])).

fof(c_0_49,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X32,X33)
      | v1_xboole_0(X33)
      | r2_hidden(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_50,plain,
    ( m1_subset_1(esk1_1(k3_tarski(X1)),X1)
    | v1_ordinal1(k3_tarski(X1))
    | ~ v1_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( v1_ordinal1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0)
    | ~ v1_ordinal1(k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,plain,
    ( v1_ordinal1(k3_tarski(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_41])).

cnf(c_0_54,plain,
    ( v1_ordinal1(X1)
    | ~ r1_tarski(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,k3_tarski(X2))
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk1_1(k3_tarski(esk7_0)),esk7_0)
    | v1_ordinal1(k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( v1_ordinal1(k3_tarski(X1))
    | ~ r2_hidden(esk1_1(k3_tarski(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,plain,
    ( v2_ordinal1(k3_tarski(X1))
    | v3_ordinal1(esk3_1(k3_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_38])).

cnf(c_0_62,negated_conjecture,
    ( v1_ordinal1(k3_tarski(esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_60])).

cnf(c_0_63,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_64,plain,(
    ! [X30,X31] :
      ( ~ v3_ordinal1(X30)
      | ~ v3_ordinal1(X31)
      | r2_hidden(X30,X31)
      | X30 = X31
      | r2_hidden(X31,X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

cnf(c_0_65,negated_conjecture,
    ( v2_ordinal1(k3_tarski(esk7_0))
    | v3_ordinal1(esk3_1(k3_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_43])).

cnf(c_0_66,negated_conjecture,
    ( ~ v2_ordinal1(k3_tarski(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_62])])).

cnf(c_0_67,plain,
    ( v2_ordinal1(k3_tarski(X1))
    | v3_ordinal1(esk2_1(k3_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_63])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( v3_ordinal1(esk3_1(k3_tarski(esk7_0))) ),
    inference(sr,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( v2_ordinal1(k3_tarski(esk7_0))
    | v3_ordinal1(esk2_1(k3_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_43])).

cnf(c_0_71,negated_conjecture,
    ( X1 = esk3_1(k3_tarski(esk7_0))
    | r2_hidden(X1,esk3_1(k3_tarski(esk7_0)))
    | r2_hidden(esk3_1(k3_tarski(esk7_0)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( v3_ordinal1(esk2_1(k3_tarski(esk7_0))) ),
    inference(sr,[status(thm)],[c_0_70,c_0_66])).

cnf(c_0_73,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk3_1(X1),esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_74,negated_conjecture,
    ( esk3_1(k3_tarski(esk7_0)) = esk2_1(k3_tarski(esk7_0))
    | r2_hidden(esk3_1(k3_tarski(esk7_0)),esk2_1(k3_tarski(esk7_0)))
    | r2_hidden(esk2_1(k3_tarski(esk7_0)),esk3_1(k3_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_75,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk2_1(X1),esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_76,negated_conjecture,
    ( esk3_1(k3_tarski(esk7_0)) = esk2_1(k3_tarski(esk7_0))
    | r2_hidden(esk2_1(k3_tarski(esk7_0)),esk3_1(k3_tarski(esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_66])).

cnf(c_0_77,plain,
    ( v2_ordinal1(X1)
    | esk2_1(X1) != esk3_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_78,negated_conjecture,
    ( esk3_1(k3_tarski(esk7_0)) = esk2_1(k3_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_66])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_66]),
    [proof]).

%------------------------------------------------------------------------------
