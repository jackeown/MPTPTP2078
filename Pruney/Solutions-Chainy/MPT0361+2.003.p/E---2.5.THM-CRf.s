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
% DateTime   : Thu Dec  3 10:46:19 EST 2020

% Result     : Theorem 0.75s
% Output     : CNFRefutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 349 expanded)
%              Number of clauses        :   72 ( 169 expanded)
%              Number of leaves         :   19 (  87 expanded)
%              Depth                    :   23
%              Number of atoms          :  202 ( 908 expanded)
%              Number of equality atoms :   57 ( 216 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

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

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t41_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(c_0_19,plain,(
    ! [X27,X28,X29,X30,X31,X32] :
      ( ( ~ r2_hidden(X29,X28)
        | r1_tarski(X29,X27)
        | X28 != k1_zfmisc_1(X27) )
      & ( ~ r1_tarski(X30,X27)
        | r2_hidden(X30,X28)
        | X28 != k1_zfmisc_1(X27) )
      & ( ~ r2_hidden(esk1_2(X31,X32),X32)
        | ~ r1_tarski(esk1_2(X31,X32),X31)
        | X32 = k1_zfmisc_1(X31) )
      & ( r2_hidden(esk1_2(X31,X32),X32)
        | r1_tarski(esk1_2(X31,X32),X31)
        | X32 = k1_zfmisc_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_20,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_21,plain,(
    ! [X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X41))
      | k3_subset_1(X41,k3_subset_1(X41,X42)) = X42 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_22,plain,(
    ! [X34,X35] :
      ( ( ~ m1_subset_1(X35,X34)
        | r2_hidden(X35,X34)
        | v1_xboole_0(X34) )
      & ( ~ r2_hidden(X35,X34)
        | m1_subset_1(X35,X34)
        | v1_xboole_0(X34) )
      & ( ~ m1_subset_1(X35,X34)
        | v1_xboole_0(X35)
        | ~ v1_xboole_0(X34) )
      & ( ~ v1_xboole_0(X35)
        | m1_subset_1(X35,X34)
        | ~ v1_xboole_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_23,plain,(
    ! [X40] : ~ v1_xboole_0(k1_zfmisc_1(X40)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(X38))
      | m1_subset_1(k3_subset_1(X38,X39),k1_zfmisc_1(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_32,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = X2
    | ~ r2_hidden(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_34,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | k3_subset_1(X36,X37) = k4_xboole_0(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_35,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_38,plain,(
    ! [X15,X16] : r1_tarski(k4_xboole_0(X15,X16),X15) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( k3_subset_1(X1,X2) = k4_xboole_0(X1,X2)
    | ~ r2_hidden(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_27]),c_0_28])).

cnf(c_0_41,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_42,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X43))
      | ~ m1_subset_1(X45,k1_zfmisc_1(X43))
      | k4_subset_1(X43,X44,X45) = k2_xboole_0(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1))
    | ~ r2_hidden(k3_subset_1(X1,X1),k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_27]),c_0_28])).

cnf(c_0_44,plain,
    ( k3_subset_1(X1,X1) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_33])).

cnf(c_0_45,plain,
    ( r2_hidden(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_41])).

cnf(c_0_46,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

fof(c_0_48,plain,(
    ! [X14] : r1_tarski(k1_xboole_0,X14) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_49,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k2_xboole_0(X9,X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_50,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k2_xboole_0(X23,X24)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_51,plain,(
    ! [X6] : k2_xboole_0(X6,X6) = X6 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_52,plain,
    ( k4_subset_1(X1,X2,X1) = k2_xboole_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_55,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t41_subset_1])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( k4_subset_1(X1,X2,X1) = k2_xboole_0(X2,X1)
    | ~ r2_hidden(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_27]),c_0_28])).

cnf(c_0_59,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_53])).

cnf(c_0_60,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_54,c_0_53])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_62,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_55])])])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,plain,
    ( k4_subset_1(X1,k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

fof(c_0_65,plain,(
    ! [X25,X26] : r1_tarski(X25,k2_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_66,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_70,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(k4_xboole_0(X20,X21),X22)
      | r1_tarski(X20,k2_xboole_0(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_71,plain,(
    ! [X17,X18,X19] : k4_xboole_0(k4_xboole_0(X17,X18),X19) = k4_xboole_0(X17,k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_72,plain,
    ( r2_hidden(k4_xboole_0(X1,X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_63])).

cnf(c_0_73,plain,
    ( k4_subset_1(X1,k4_xboole_0(X2,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_64,c_0_63])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_75,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_28])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_79,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_80,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),X2) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_72]),c_0_73])).

fof(c_0_81,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk4_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_75])).

cnf(c_0_84,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X3,X4))
    | ~ r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X4) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_75,c_0_80])).

cnf(c_0_86,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_79]),c_0_79]),c_0_79])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_89,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),k2_xboole_0(X2,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_63]),c_0_53])])).

cnf(c_0_90,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(k2_xboole_0(X2,X3),X4),k2_xboole_0(X2,k2_xboole_0(X3,X4)))) = X1 ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_92,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X1,esk4_0),X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,esk4_0),k2_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_94]),c_0_28])).

cnf(c_0_97,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_98,negated_conjecture,
    ( k3_subset_1(esk2_0,esk3_0) = k4_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( k4_subset_1(esk2_0,X1,esk4_0) = k2_xboole_0(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_69])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,esk4_0),k2_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_75])).

cnf(c_0_101,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_96]),c_0_75])).

cnf(c_0_102,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,esk4_0) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_94])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_105,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_104])).

cnf(c_0_107,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)),k1_zfmisc_1(k4_xboole_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_67])).

cnf(c_0_108,negated_conjecture,
    ( k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)) = k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_106])).

cnf(c_0_109,plain,
    ( r2_hidden(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k1_zfmisc_1(k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_79])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_108]),c_0_109])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:43:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.75/0.92  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.75/0.92  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.75/0.92  #
% 0.75/0.92  # Preprocessing time       : 0.041 s
% 0.75/0.92  # Presaturation interreduction done
% 0.75/0.92  
% 0.75/0.92  # Proof found!
% 0.75/0.92  # SZS status Theorem
% 0.75/0.92  # SZS output start CNFRefutation
% 0.75/0.92  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.75/0.92  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.75/0.92  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.75/0.92  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.75/0.92  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.75/0.92  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.75/0.92  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.75/0.92  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.75/0.92  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.75/0.92  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.75/0.92  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.75/0.92  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.75/0.92  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.75/0.92  fof(t41_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 0.75/0.92  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.75/0.92  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.75/0.92  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.75/0.92  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.75/0.92  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.75/0.92  fof(c_0_19, plain, ![X27, X28, X29, X30, X31, X32]:(((~r2_hidden(X29,X28)|r1_tarski(X29,X27)|X28!=k1_zfmisc_1(X27))&(~r1_tarski(X30,X27)|r2_hidden(X30,X28)|X28!=k1_zfmisc_1(X27)))&((~r2_hidden(esk1_2(X31,X32),X32)|~r1_tarski(esk1_2(X31,X32),X31)|X32=k1_zfmisc_1(X31))&(r2_hidden(esk1_2(X31,X32),X32)|r1_tarski(esk1_2(X31,X32),X31)|X32=k1_zfmisc_1(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.75/0.92  fof(c_0_20, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.75/0.92  fof(c_0_21, plain, ![X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(X41))|k3_subset_1(X41,k3_subset_1(X41,X42))=X42), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.75/0.92  fof(c_0_22, plain, ![X34, X35]:(((~m1_subset_1(X35,X34)|r2_hidden(X35,X34)|v1_xboole_0(X34))&(~r2_hidden(X35,X34)|m1_subset_1(X35,X34)|v1_xboole_0(X34)))&((~m1_subset_1(X35,X34)|v1_xboole_0(X35)|~v1_xboole_0(X34))&(~v1_xboole_0(X35)|m1_subset_1(X35,X34)|~v1_xboole_0(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.75/0.92  fof(c_0_23, plain, ![X40]:~v1_xboole_0(k1_zfmisc_1(X40)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.75/0.92  cnf(c_0_24, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.75/0.92  cnf(c_0_25, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.75/0.92  cnf(c_0_26, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.75/0.92  cnf(c_0_27, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.75/0.92  cnf(c_0_28, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.75/0.92  cnf(c_0_29, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_24])).
% 0.75/0.92  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_25])).
% 0.75/0.92  fof(c_0_31, plain, ![X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(X38))|m1_subset_1(k3_subset_1(X38,X39),k1_zfmisc_1(X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.75/0.92  cnf(c_0_32, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=X2|~r2_hidden(X2,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.75/0.92  cnf(c_0_33, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.75/0.92  fof(c_0_34, plain, ![X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(X36))|k3_subset_1(X36,X37)=k4_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.75/0.92  cnf(c_0_35, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.75/0.92  cnf(c_0_36, plain, (k3_subset_1(X1,k3_subset_1(X1,X1))=X1), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.75/0.92  cnf(c_0_37, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.75/0.92  fof(c_0_38, plain, ![X15, X16]:r1_tarski(k4_xboole_0(X15,X16),X15), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.75/0.92  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))|~m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.75/0.92  cnf(c_0_40, plain, (k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)|~r2_hidden(X2,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_27]), c_0_28])).
% 0.75/0.92  cnf(c_0_41, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.75/0.92  fof(c_0_42, plain, ![X43, X44, X45]:(~m1_subset_1(X44,k1_zfmisc_1(X43))|~m1_subset_1(X45,k1_zfmisc_1(X43))|k4_subset_1(X43,X44,X45)=k2_xboole_0(X44,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.75/0.92  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))|~r2_hidden(k3_subset_1(X1,X1),k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_27]), c_0_28])).
% 0.75/0.92  cnf(c_0_44, plain, (k3_subset_1(X1,X1)=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_40, c_0_33])).
% 0.75/0.92  cnf(c_0_45, plain, (r2_hidden(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_29, c_0_41])).
% 0.75/0.92  cnf(c_0_46, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.75/0.92  cnf(c_0_47, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.75/0.92  fof(c_0_48, plain, ![X14]:r1_tarski(k1_xboole_0,X14), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.75/0.92  fof(c_0_49, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k2_xboole_0(X9,X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.75/0.92  fof(c_0_50, plain, ![X23, X24]:k4_xboole_0(X23,k2_xboole_0(X23,X24))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.75/0.92  fof(c_0_51, plain, ![X6]:k2_xboole_0(X6,X6)=X6, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.75/0.92  cnf(c_0_52, plain, (k4_subset_1(X1,X2,X1)=k2_xboole_0(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.75/0.92  cnf(c_0_53, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.75/0.92  cnf(c_0_54, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.75/0.92  fof(c_0_55, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2))))), inference(assume_negation,[status(cth)],[t41_subset_1])).
% 0.75/0.92  cnf(c_0_56, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.75/0.92  cnf(c_0_57, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.75/0.92  cnf(c_0_58, plain, (k4_subset_1(X1,X2,X1)=k2_xboole_0(X2,X1)|~r2_hidden(X2,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_27]), c_0_28])).
% 0.75/0.92  cnf(c_0_59, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_29, c_0_53])).
% 0.75/0.92  cnf(c_0_60, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_54, c_0_53])).
% 0.75/0.92  cnf(c_0_61, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.75/0.92  fof(c_0_62, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_55])])])).
% 0.75/0.92  cnf(c_0_63, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.75/0.92  cnf(c_0_64, plain, (k4_subset_1(X1,k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.75/0.92  fof(c_0_65, plain, ![X25, X26]:r1_tarski(X25,k2_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.75/0.92  fof(c_0_66, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.75/0.92  cnf(c_0_67, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_61])).
% 0.75/0.92  cnf(c_0_68, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.75/0.92  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.75/0.92  fof(c_0_70, plain, ![X20, X21, X22]:(~r1_tarski(k4_xboole_0(X20,X21),X22)|r1_tarski(X20,k2_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.75/0.92  fof(c_0_71, plain, ![X17, X18, X19]:k4_xboole_0(k4_xboole_0(X17,X18),X19)=k4_xboole_0(X17,k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.75/0.92  cnf(c_0_72, plain, (r2_hidden(k4_xboole_0(X1,X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_59, c_0_63])).
% 0.75/0.92  cnf(c_0_73, plain, (k4_subset_1(X1,k4_xboole_0(X2,X2),X1)=X1), inference(spm,[status(thm)],[c_0_64, c_0_63])).
% 0.75/0.92  cnf(c_0_74, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.75/0.92  cnf(c_0_75, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.75/0.92  cnf(c_0_76, plain, (k2_xboole_0(X1,X2)=X2|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_54, c_0_67])).
% 0.75/0.92  cnf(c_0_77, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_28])).
% 0.75/0.92  cnf(c_0_78, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.75/0.92  cnf(c_0_79, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.75/0.92  cnf(c_0_80, plain, (k2_xboole_0(k4_xboole_0(X1,X1),X2)=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_72]), c_0_73])).
% 0.75/0.92  fof(c_0_81, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X12,X13)|r1_tarski(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.75/0.92  cnf(c_0_82, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.75/0.92  cnf(c_0_83, negated_conjecture, (k2_xboole_0(esk2_0,esk4_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_75])).
% 0.75/0.92  cnf(c_0_84, plain, (r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X3,X4))|~r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X4)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.75/0.92  cnf(c_0_85, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_75, c_0_80])).
% 0.75/0.92  cnf(c_0_86, plain, (k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))=k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_79]), c_0_79]), c_0_79])).
% 0.75/0.92  cnf(c_0_87, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.75/0.92  cnf(c_0_88, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.75/0.92  cnf(c_0_89, plain, (r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),k2_xboole_0(X2,X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_63]), c_0_53])])).
% 0.75/0.92  cnf(c_0_90, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(k2_xboole_0(X2,X3),X4),k2_xboole_0(X2,k2_xboole_0(X3,X4))))=X1), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.75/0.92  cnf(c_0_91, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.75/0.92  cnf(c_0_92, plain, (r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.75/0.92  cnf(c_0_93, negated_conjecture, (r1_tarski(k4_xboole_0(k2_xboole_0(X1,esk4_0),X1),esk2_0)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.75/0.92  cnf(c_0_94, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.75/0.92  cnf(c_0_95, negated_conjecture, (r1_tarski(k2_xboole_0(X1,esk4_0),k2_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_78, c_0_93])).
% 0.75/0.92  cnf(c_0_96, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_94]), c_0_28])).
% 0.75/0.92  cnf(c_0_97, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.75/0.92  cnf(c_0_98, negated_conjecture, (k3_subset_1(esk2_0,esk3_0)=k4_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_94])).
% 0.75/0.92  cnf(c_0_99, negated_conjecture, (k4_subset_1(esk2_0,X1,esk4_0)=k2_xboole_0(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_46, c_0_69])).
% 0.75/0.92  cnf(c_0_100, negated_conjecture, (r1_tarski(k2_xboole_0(X1,esk4_0),k2_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_95, c_0_75])).
% 0.75/0.92  cnf(c_0_101, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_96]), c_0_75])).
% 0.75/0.92  cnf(c_0_102, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,k4_subset_1(esk2_0,esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_97, c_0_98])).
% 0.75/0.92  cnf(c_0_103, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,esk4_0)=k2_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_99, c_0_94])).
% 0.75/0.92  cnf(c_0_104, negated_conjecture, (r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.75/0.92  cnf(c_0_105, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_102, c_0_103])).
% 0.75/0.92  cnf(c_0_106, negated_conjecture, (r2_hidden(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_29, c_0_104])).
% 0.75/0.92  cnf(c_0_107, negated_conjecture, (~r2_hidden(k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0)),k1_zfmisc_1(k4_xboole_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_105, c_0_67])).
% 0.75/0.92  cnf(c_0_108, negated_conjecture, (k3_subset_1(esk2_0,k2_xboole_0(esk3_0,esk4_0))=k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_106])).
% 0.75/0.92  cnf(c_0_109, plain, (r2_hidden(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k1_zfmisc_1(k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_45, c_0_79])).
% 0.75/0.92  cnf(c_0_110, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_108]), c_0_109])]), ['proof']).
% 0.75/0.92  # SZS output end CNFRefutation
% 0.75/0.92  # Proof object total steps             : 111
% 0.75/0.92  # Proof object clause steps            : 72
% 0.75/0.92  # Proof object formula steps           : 39
% 0.75/0.92  # Proof object conjectures             : 25
% 0.75/0.92  # Proof object clause conjectures      : 22
% 0.75/0.92  # Proof object formula conjectures     : 3
% 0.75/0.92  # Proof object initial clauses used    : 23
% 0.75/0.92  # Proof object initial formulas used   : 19
% 0.75/0.92  # Proof object generating inferences   : 42
% 0.75/0.92  # Proof object simplifying inferences  : 25
% 0.75/0.92  # Training examples: 0 positive, 0 negative
% 0.75/0.92  # Parsed axioms                        : 19
% 0.75/0.92  # Removed by relevancy pruning/SinE    : 0
% 0.75/0.92  # Initial clauses                      : 29
% 0.75/0.92  # Removed in clause preprocessing      : 0
% 0.75/0.92  # Initial clauses in saturation        : 29
% 0.75/0.92  # Processed clauses                    : 4826
% 0.75/0.92  # ...of these trivial                  : 314
% 0.75/0.92  # ...subsumed                          : 3456
% 0.75/0.92  # ...remaining for further processing  : 1056
% 0.75/0.92  # Other redundant clauses eliminated   : 4
% 0.75/0.92  # Clauses deleted for lack of memory   : 0
% 0.75/0.92  # Backward-subsumed                    : 11
% 0.75/0.92  # Backward-rewritten                   : 124
% 0.75/0.92  # Generated clauses                    : 51023
% 0.75/0.92  # ...of the previous two non-trivial   : 34650
% 0.75/0.92  # Contextual simplify-reflections      : 5
% 0.75/0.92  # Paramodulations                      : 51017
% 0.75/0.92  # Factorizations                       : 2
% 0.75/0.92  # Equation resolutions                 : 4
% 0.75/0.92  # Propositional unsat checks           : 0
% 0.75/0.92  #    Propositional check models        : 0
% 0.75/0.92  #    Propositional check unsatisfiable : 0
% 0.75/0.92  #    Propositional clauses             : 0
% 0.75/0.92  #    Propositional clauses after purity: 0
% 0.75/0.92  #    Propositional unsat core size     : 0
% 0.75/0.92  #    Propositional preprocessing time  : 0.000
% 0.75/0.92  #    Propositional encoding time       : 0.000
% 0.75/0.92  #    Propositional solver time         : 0.000
% 0.75/0.92  #    Success case prop preproc time    : 0.000
% 0.75/0.92  #    Success case prop encoding time   : 0.000
% 0.75/0.92  #    Success case prop solver time     : 0.000
% 0.75/0.92  # Current number of processed clauses  : 889
% 0.75/0.92  #    Positive orientable unit clauses  : 312
% 0.75/0.92  #    Positive unorientable unit clauses: 25
% 0.75/0.92  #    Negative unit clauses             : 1
% 0.75/0.92  #    Non-unit-clauses                  : 551
% 0.75/0.92  # Current number of unprocessed clauses: 29797
% 0.75/0.92  # ...number of literals in the above   : 56829
% 0.75/0.92  # Current number of archived formulas  : 0
% 0.75/0.92  # Current number of archived clauses   : 163
% 0.75/0.92  # Clause-clause subsumption calls (NU) : 84882
% 0.75/0.92  # Rec. Clause-clause subsumption calls : 66661
% 0.75/0.92  # Non-unit clause-clause subsumptions  : 2890
% 0.75/0.92  # Unit Clause-clause subsumption calls : 4345
% 0.75/0.92  # Rewrite failures with RHS unbound    : 400
% 0.75/0.92  # BW rewrite match attempts            : 2242
% 0.75/0.92  # BW rewrite match successes           : 145
% 0.75/0.92  # Condensation attempts                : 0
% 0.75/0.92  # Condensation successes               : 0
% 0.75/0.92  # Termbank termtop insertions          : 517732
% 0.75/0.92  
% 0.75/0.92  # -------------------------------------------------
% 0.75/0.92  # User time                : 0.532 s
% 0.75/0.92  # System time              : 0.030 s
% 0.75/0.92  # Total time               : 0.562 s
% 0.75/0.92  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
