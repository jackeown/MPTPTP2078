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
% DateTime   : Thu Dec  3 10:46:11 EST 2020

% Result     : Theorem 0.41s
% Output     : CNFRefutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 268 expanded)
%              Number of clauses        :   53 ( 125 expanded)
%              Number of leaves         :   15 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          :  204 ( 749 expanded)
%              Number of equality atoms :   23 (  69 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t40_subset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X2,k3_subset_1(X1,X3)) )
       => X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(t31_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(t38_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(c_0_15,plain,(
    ! [X26] : m1_subset_1(k2_subset_1(X26),k1_zfmisc_1(X26)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_16,plain,(
    ! [X25] : k2_subset_1(X25) = X25 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_17,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X23,X22)
        | r2_hidden(X23,X22)
        | v1_xboole_0(X22) )
      & ( ~ r2_hidden(X23,X22)
        | m1_subset_1(X23,X22)
        | v1_xboole_0(X22) )
      & ( ~ m1_subset_1(X23,X22)
        | v1_xboole_0(X23)
        | ~ v1_xboole_0(X22) )
      & ( ~ v1_xboole_0(X23)
        | m1_subset_1(X23,X22)
        | ~ v1_xboole_0(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_18,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X27] : ~ v1_xboole_0(k1_zfmisc_1(X27)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_21,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X1))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X2,k3_subset_1(X1,X3)) )
         => X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t40_subset_1])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_30,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | r1_tarski(k1_zfmisc_1(X19),k1_zfmisc_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

fof(c_0_31,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | r1_tarski(X17,k3_tarski(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & r1_tarski(esk3_0,esk4_0)
    & r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0))
    & esk3_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

fof(c_0_33,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X13,X14)
      | r1_tarski(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(esk1_2(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X21] : k3_tarski(k1_zfmisc_1(X21)) = X21 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(esk1_2(X1,k1_zfmisc_1(X2)),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( r1_tarski(esk1_2(X1,X2),k3_tarski(X1))
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_38]),c_0_24])).

cnf(c_0_44,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k1_zfmisc_1(X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_43]),c_0_44])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_47])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(X1),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_29])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(X1,k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(k3_tarski(X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_52,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(X3),X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_35])).

fof(c_0_54,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | ~ v1_xboole_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_44])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_35])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_59,plain,(
    ! [X28,X29,X30] :
      ( ( ~ r1_tarski(X29,X30)
        | r1_tarski(k3_subset_1(X28,X30),k3_subset_1(X28,X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(X28)) )
      & ( ~ r1_tarski(k3_subset_1(X28,X30),k3_subset_1(X28,X29))
        | r1_tarski(X29,X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(X2,esk4_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_55])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,plain,
    ( r1_tarski(k3_subset_1(X3,X2),k3_subset_1(X3,X1))
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | ~ r1_tarski(k1_zfmisc_1(X2),X1)
    | ~ r1_tarski(esk4_0,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_64])).

fof(c_0_69,plain,(
    ! [X31,X32] :
      ( ( ~ r1_tarski(X32,k3_subset_1(X31,X32))
        | X32 = k1_subset_1(X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(X31)) )
      & ( X32 != k1_subset_1(X31)
        | r1_tarski(X32,k3_subset_1(X31,X32))
        | ~ m1_subset_1(X32,k1_zfmisc_1(X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_subset_1])])])).

fof(c_0_70,plain,(
    ! [X24] : k1_subset_1(X24) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_38])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(esk4_0,X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_55])).

cnf(c_0_74,plain,
    ( X1 = k1_subset_1(X2)
    | ~ r1_tarski(X1,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_75,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk2_0,X2))
    | ~ r1_tarski(X1,k3_subset_1(esk2_0,esk4_0))
    | ~ r1_tarski(X2,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_71]),c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_63]),c_0_63])])).

cnf(c_0_79,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk3_0,k3_subset_1(esk2_0,X1))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_58])]),c_0_82]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.41/0.59  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.41/0.59  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.41/0.59  #
% 0.41/0.59  # Preprocessing time       : 0.029 s
% 0.41/0.59  # Presaturation interreduction done
% 0.41/0.59  
% 0.41/0.59  # Proof found!
% 0.41/0.59  # SZS status Theorem
% 0.41/0.59  # SZS output start CNFRefutation
% 0.41/0.59  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.41/0.59  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.41/0.59  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.41/0.59  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.41/0.59  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.41/0.59  fof(t40_subset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 0.41/0.59  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 0.41/0.59  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.41/0.59  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.41/0.59  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.41/0.59  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.41/0.59  fof(t7_boole, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 0.41/0.59  fof(t31_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 0.41/0.59  fof(t38_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 0.41/0.59  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 0.41/0.59  fof(c_0_15, plain, ![X26]:m1_subset_1(k2_subset_1(X26),k1_zfmisc_1(X26)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.41/0.59  fof(c_0_16, plain, ![X25]:k2_subset_1(X25)=X25, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.41/0.59  fof(c_0_17, plain, ![X22, X23]:(((~m1_subset_1(X23,X22)|r2_hidden(X23,X22)|v1_xboole_0(X22))&(~r2_hidden(X23,X22)|m1_subset_1(X23,X22)|v1_xboole_0(X22)))&((~m1_subset_1(X23,X22)|v1_xboole_0(X23)|~v1_xboole_0(X22))&(~v1_xboole_0(X23)|m1_subset_1(X23,X22)|~v1_xboole_0(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.41/0.59  cnf(c_0_18, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.41/0.59  cnf(c_0_19, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.41/0.59  fof(c_0_20, plain, ![X27]:~v1_xboole_0(k1_zfmisc_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.41/0.59  fof(c_0_21, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.41/0.59  cnf(c_0_22, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.41/0.59  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.41/0.59  cnf(c_0_24, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.41/0.59  cnf(c_0_25, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.41/0.59  cnf(c_0_26, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.41/0.59  fof(c_0_27, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t40_subset_1])).
% 0.41/0.59  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.41/0.59  cnf(c_0_29, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_zfmisc_1(X1),X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.41/0.59  fof(c_0_30, plain, ![X19, X20]:(~r1_tarski(X19,X20)|r1_tarski(k1_zfmisc_1(X19),k1_zfmisc_1(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 0.41/0.59  fof(c_0_31, plain, ![X17, X18]:(~r2_hidden(X17,X18)|r1_tarski(X17,k3_tarski(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.41/0.59  fof(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((r1_tarski(esk3_0,esk4_0)&r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0)))&esk3_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.41/0.59  fof(c_0_33, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X13,X14)|r1_tarski(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.41/0.59  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~r1_tarski(k1_zfmisc_1(esk1_2(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.41/0.59  cnf(c_0_35, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.41/0.59  cnf(c_0_36, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.41/0.59  cnf(c_0_37, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.41/0.59  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.41/0.59  fof(c_0_39, plain, ![X21]:k3_tarski(k1_zfmisc_1(X21))=X21, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.41/0.59  cnf(c_0_40, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.41/0.59  cnf(c_0_41, plain, (r1_tarski(X1,k1_zfmisc_1(X2))|~r1_tarski(esk1_2(X1,k1_zfmisc_1(X2)),X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.41/0.59  cnf(c_0_42, plain, (r1_tarski(esk1_2(X1,X2),k3_tarski(X1))|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.41/0.59  cnf(c_0_43, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_38]), c_0_24])).
% 0.41/0.59  cnf(c_0_44, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.41/0.59  cnf(c_0_45, plain, (r1_tarski(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k1_zfmisc_1(X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_40, c_0_35])).
% 0.41/0.59  cnf(c_0_46, plain, (r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.41/0.59  cnf(c_0_47, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_43]), c_0_44])).
% 0.41/0.59  cnf(c_0_48, plain, (r1_tarski(X1,k1_zfmisc_1(X2))|~r1_tarski(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.41/0.59  cnf(c_0_49, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_47])).
% 0.41/0.59  cnf(c_0_50, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_zfmisc_1(X1),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_25, c_0_29])).
% 0.41/0.59  cnf(c_0_51, negated_conjecture, (r1_tarski(X1,k1_zfmisc_1(esk2_0))|~r1_tarski(k3_tarski(X1),esk4_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.41/0.59  fof(c_0_52, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.41/0.59  cnf(c_0_53, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_zfmisc_1(X3),X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_50, c_0_35])).
% 0.41/0.59  fof(c_0_54, plain, ![X15, X16]:(~r2_hidden(X15,X16)|~v1_xboole_0(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).
% 0.41/0.59  cnf(c_0_55, negated_conjecture, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(esk2_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_44])).
% 0.41/0.59  cnf(c_0_56, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.41/0.59  cnf(c_0_57, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_53, c_0_35])).
% 0.41/0.59  cnf(c_0_58, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.41/0.59  fof(c_0_59, plain, ![X28, X29, X30]:((~r1_tarski(X29,X30)|r1_tarski(k3_subset_1(X28,X30),k3_subset_1(X28,X29))|~m1_subset_1(X30,k1_zfmisc_1(X28))|~m1_subset_1(X29,k1_zfmisc_1(X28)))&(~r1_tarski(k3_subset_1(X28,X30),k3_subset_1(X28,X29))|r1_tarski(X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(X28))|~m1_subset_1(X29,k1_zfmisc_1(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).
% 0.41/0.59  cnf(c_0_60, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.41/0.59  cnf(c_0_61, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.41/0.59  cnf(c_0_62, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(esk2_0))|~r1_tarski(X2,esk4_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_53, c_0_55])).
% 0.41/0.59  cnf(c_0_63, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_56])).
% 0.41/0.59  cnf(c_0_64, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(X1))|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.41/0.59  cnf(c_0_65, plain, (r1_tarski(k3_subset_1(X3,X2),k3_subset_1(X3,X1))|~r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.41/0.59  cnf(c_0_66, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_60, c_0_61])).
% 0.41/0.59  cnf(c_0_67, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(esk2_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.41/0.59  cnf(c_0_68, negated_conjecture, (r2_hidden(esk3_0,X1)|~r1_tarski(k1_zfmisc_1(X2),X1)|~r1_tarski(esk4_0,X2)), inference(spm,[status(thm)],[c_0_25, c_0_64])).
% 0.41/0.59  fof(c_0_69, plain, ![X31, X32]:((~r1_tarski(X32,k3_subset_1(X31,X32))|X32=k1_subset_1(X31)|~m1_subset_1(X32,k1_zfmisc_1(X31)))&(X32!=k1_subset_1(X31)|r1_tarski(X32,k3_subset_1(X31,X32))|~m1_subset_1(X32,k1_zfmisc_1(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_subset_1])])])).
% 0.41/0.59  fof(c_0_70, plain, ![X24]:k1_subset_1(X24)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.41/0.59  cnf(c_0_71, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_65, c_0_38])).
% 0.41/0.59  cnf(c_0_72, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.41/0.59  cnf(c_0_73, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))|~r1_tarski(esk4_0,X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_68, c_0_55])).
% 0.41/0.59  cnf(c_0_74, plain, (X1=k1_subset_1(X2)|~r1_tarski(X1,k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.41/0.59  cnf(c_0_75, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.41/0.59  cnf(c_0_76, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk2_0,X2))|~r1_tarski(X1,k3_subset_1(esk2_0,esk4_0))|~r1_tarski(X2,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_71]), c_0_72])).
% 0.41/0.59  cnf(c_0_77, negated_conjecture, (r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.41/0.59  cnf(c_0_78, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_63]), c_0_63])])).
% 0.41/0.59  cnf(c_0_79, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X1))), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 0.41/0.59  cnf(c_0_80, negated_conjecture, (r1_tarski(esk3_0,k3_subset_1(esk2_0,X1))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.41/0.59  cnf(c_0_81, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_66, c_0_78])).
% 0.41/0.59  cnf(c_0_82, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.41/0.59  cnf(c_0_83, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81]), c_0_58])]), c_0_82]), ['proof']).
% 0.41/0.59  # SZS output end CNFRefutation
% 0.41/0.59  # Proof object total steps             : 84
% 0.41/0.59  # Proof object clause steps            : 53
% 0.41/0.59  # Proof object formula steps           : 31
% 0.41/0.59  # Proof object conjectures             : 24
% 0.41/0.59  # Proof object clause conjectures      : 21
% 0.41/0.59  # Proof object formula conjectures     : 3
% 0.41/0.59  # Proof object initial clauses used    : 21
% 0.41/0.59  # Proof object initial formulas used   : 15
% 0.41/0.59  # Proof object generating inferences   : 28
% 0.41/0.59  # Proof object simplifying inferences  : 14
% 0.41/0.59  # Training examples: 0 positive, 0 negative
% 0.41/0.59  # Parsed axioms                        : 15
% 0.41/0.59  # Removed by relevancy pruning/SinE    : 0
% 0.41/0.59  # Initial clauses                      : 27
% 0.41/0.59  # Removed in clause preprocessing      : 2
% 0.41/0.59  # Initial clauses in saturation        : 25
% 0.41/0.59  # Processed clauses                    : 2922
% 0.41/0.59  # ...of these trivial                  : 31
% 0.41/0.59  # ...subsumed                          : 1970
% 0.41/0.59  # ...remaining for further processing  : 921
% 0.41/0.59  # Other redundant clauses eliminated   : 3
% 0.41/0.59  # Clauses deleted for lack of memory   : 0
% 0.41/0.59  # Backward-subsumed                    : 43
% 0.41/0.59  # Backward-rewritten                   : 8
% 0.41/0.59  # Generated clauses                    : 15543
% 0.41/0.59  # ...of the previous two non-trivial   : 14462
% 0.41/0.59  # Contextual simplify-reflections      : 31
% 0.41/0.59  # Paramodulations                      : 15540
% 0.41/0.59  # Factorizations                       : 0
% 0.41/0.59  # Equation resolutions                 : 3
% 0.41/0.59  # Propositional unsat checks           : 0
% 0.41/0.59  #    Propositional check models        : 0
% 0.41/0.59  #    Propositional check unsatisfiable : 0
% 0.41/0.59  #    Propositional clauses             : 0
% 0.41/0.59  #    Propositional clauses after purity: 0
% 0.41/0.59  #    Propositional unsat core size     : 0
% 0.41/0.59  #    Propositional preprocessing time  : 0.000
% 0.41/0.59  #    Propositional encoding time       : 0.000
% 0.41/0.59  #    Propositional solver time         : 0.000
% 0.41/0.59  #    Success case prop preproc time    : 0.000
% 0.41/0.59  #    Success case prop encoding time   : 0.000
% 0.41/0.59  #    Success case prop solver time     : 0.000
% 0.41/0.59  # Current number of processed clauses  : 843
% 0.41/0.59  #    Positive orientable unit clauses  : 35
% 0.41/0.59  #    Positive unorientable unit clauses: 0
% 0.41/0.59  #    Negative unit clauses             : 5
% 0.41/0.59  #    Non-unit-clauses                  : 803
% 0.41/0.59  # Current number of unprocessed clauses: 11536
% 0.41/0.59  # ...number of literals in the above   : 50222
% 0.41/0.59  # Current number of archived formulas  : 0
% 0.41/0.59  # Current number of archived clauses   : 77
% 0.41/0.59  # Clause-clause subsumption calls (NU) : 106885
% 0.41/0.59  # Rec. Clause-clause subsumption calls : 88061
% 0.41/0.59  # Non-unit clause-clause subsumptions  : 1321
% 0.41/0.59  # Unit Clause-clause subsumption calls : 172
% 0.41/0.59  # Rewrite failures with RHS unbound    : 0
% 0.41/0.59  # BW rewrite match attempts            : 48
% 0.41/0.59  # BW rewrite match successes           : 3
% 0.41/0.59  # Condensation attempts                : 0
% 0.41/0.59  # Condensation successes               : 0
% 0.41/0.59  # Termbank termtop insertions          : 200151
% 0.41/0.59  
% 0.41/0.59  # -------------------------------------------------
% 0.41/0.59  # User time                : 0.241 s
% 0.41/0.59  # System time              : 0.007 s
% 0.41/0.59  # Total time               : 0.248 s
% 0.41/0.59  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
