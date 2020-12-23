%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:43 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 424 expanded)
%              Number of clauses        :   54 ( 189 expanded)
%              Number of leaves         :   16 ( 113 expanded)
%              Depth                    :   11
%              Number of atoms          :  146 ( 839 expanded)
%              Number of equality atoms :   68 ( 337 expanded)
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

fof(t32_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

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

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t50_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

fof(t83_zfmisc_1,axiom,(
    ! [X1,X2] : k1_zfmisc_1(k3_xboole_0(X1,X2)) = k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_zfmisc_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(c_0_16,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X30,X29)
        | r1_tarski(X30,X28)
        | X29 != k1_zfmisc_1(X28) )
      & ( ~ r1_tarski(X31,X28)
        | r2_hidden(X31,X29)
        | X29 != k1_zfmisc_1(X28) )
      & ( ~ r2_hidden(esk2_2(X32,X33),X33)
        | ~ r1_tarski(esk2_2(X32,X33),X32)
        | X33 = k1_zfmisc_1(X32) )
      & ( r2_hidden(esk2_2(X32,X33),X33)
        | r1_tarski(esk2_2(X32,X33),X32)
        | X33 = k1_zfmisc_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t32_subset_1])).

fof(c_0_18,plain,(
    ! [X41,X42] : m1_subset_1(k6_subset_1(X41,X42),k1_zfmisc_1(X41)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_19,plain,(
    ! [X44,X45] : k6_subset_1(X44,X45) = k4_xboole_0(X44,X45) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_20,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k3_xboole_0(X18,X19) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X37,X38] :
      ( ( ~ m1_subset_1(X38,X37)
        | r2_hidden(X38,X37)
        | v1_xboole_0(X37) )
      & ( ~ r2_hidden(X38,X37)
        | m1_subset_1(X38,X37)
        | v1_xboole_0(X37) )
      & ( ~ m1_subset_1(X38,X37)
        | v1_xboole_0(X38)
        | ~ v1_xboole_0(X37) )
      & ( ~ v1_xboole_0(X38)
        | m1_subset_1(X38,X37)
        | ~ v1_xboole_0(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
    & k7_subset_1(esk3_0,esk4_0,esk5_0) != k9_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_25,plain,(
    ! [X43] : ~ v1_xboole_0(k1_zfmisc_1(X43)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_26,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_34,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_35,plain,(
    ! [X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X39))
      | k3_subset_1(X39,X40) = k4_xboole_0(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_36,plain,(
    ! [X46,X47,X48] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(X46))
      | k7_subset_1(X46,X47,X48) = k4_xboole_0(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_37,plain,(
    ! [X22,X23,X24] : k3_xboole_0(X22,k4_xboole_0(X23,X24)) = k4_xboole_0(k3_xboole_0(X22,X23),X24) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_38,plain,(
    ! [X25,X26,X27] : k3_xboole_0(X25,k4_xboole_0(X26,X27)) = k4_xboole_0(k3_xboole_0(X25,X26),k3_xboole_0(X25,X27)) ),
    inference(variable_rename,[status(thm)],[t50_xboole_1])).

cnf(c_0_39,plain,
    ( m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_45,plain,(
    ! [X35,X36] : k1_zfmisc_1(k3_xboole_0(X35,X36)) = k3_xboole_0(k1_zfmisc_1(X35),k1_zfmisc_1(X36)) ),
    inference(variable_rename,[status(thm)],[t83_zfmisc_1])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_48,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k4_xboole_0(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_49,plain,
    ( r2_hidden(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_39]),c_0_33])).

cnf(c_0_50,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_51,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_28])).

cnf(c_0_52,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_28])).

cnf(c_0_53,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_55,plain,
    ( k1_zfmisc_1(k3_xboole_0(X1,X2)) = k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_28]),c_0_28])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_28]),c_0_28])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k5_xboole_0(esk3_0,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( k7_subset_1(esk3_0,esk4_0,esk5_0) != k9_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_61,negated_conjecture,
    ( k3_subset_1(esk3_0,esk5_0) = k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_32])).

cnf(c_0_62,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_33])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_54]),c_0_33])).

cnf(c_0_64,plain,
    ( k3_subset_1(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ m1_subset_1(X3,k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_55]),c_0_56])).

cnf(c_0_65,plain,
    ( m1_subset_1(k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))),k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_55]),c_0_56])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X1,X3)))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_57,c_0_56])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_28]),c_0_28])).

cnf(c_0_68,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk5_0)) = k5_xboole_0(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_59]),c_0_42])).

cnf(c_0_69,negated_conjecture,
    ( k9_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0))) != k7_subset_1(esk3_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( k7_subset_1(esk3_0,esk4_0,X1) = k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_71,plain,(
    ! [X49,X50,X51] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(X49))
      | k9_subset_1(X49,X50,X51) = k3_xboole_0(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_72,plain,
    ( k3_subset_1(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_50]),c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( k9_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0))) != k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k5_xboole_0(esk3_0,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_50])).

cnf(c_0_77,negated_conjecture,
    ( k3_subset_1(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk5_0)) = k3_xboole_0(X1,k5_xboole_0(esk3_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_68]),c_0_73])).

cnf(c_0_78,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_67])).

cnf(c_0_79,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_66]),c_0_67])).

cnf(c_0_80,negated_conjecture,
    ( k9_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,esk5_0)) != k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_50])).

cnf(c_0_81,negated_conjecture,
    ( k9_subset_1(esk3_0,X1,k5_xboole_0(esk3_0,esk5_0)) = k3_xboole_0(X1,k5_xboole_0(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( k3_subset_1(k3_xboole_0(esk3_0,X1),k3_xboole_0(X1,esk5_0)) = k3_xboole_0(X1,k5_xboole_0(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_42])).

cnf(c_0_83,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_63]),c_0_42])).

cnf(c_0_84,plain,
    ( k3_subset_1(X1,k3_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_78]),c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0)) != k3_xboole_0(esk4_0,k5_xboole_0(esk3_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_85]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:02:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.67  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.47/0.67  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.47/0.67  #
% 0.47/0.67  # Preprocessing time       : 0.028 s
% 0.47/0.67  # Presaturation interreduction done
% 0.47/0.67  
% 0.47/0.67  # Proof found!
% 0.47/0.67  # SZS status Theorem
% 0.47/0.67  # SZS output start CNFRefutation
% 0.47/0.67  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.47/0.67  fof(t32_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 0.47/0.67  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 0.47/0.67  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.47/0.67  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.47/0.67  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.47/0.67  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.47/0.67  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.47/0.67  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.47/0.67  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.47/0.67  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.47/0.67  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.47/0.67  fof(t50_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_xboole_1)).
% 0.47/0.67  fof(t83_zfmisc_1, axiom, ![X1, X2]:k1_zfmisc_1(k3_xboole_0(X1,X2))=k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_zfmisc_1)).
% 0.47/0.67  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.47/0.67  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.47/0.67  fof(c_0_16, plain, ![X28, X29, X30, X31, X32, X33]:(((~r2_hidden(X30,X29)|r1_tarski(X30,X28)|X29!=k1_zfmisc_1(X28))&(~r1_tarski(X31,X28)|r2_hidden(X31,X29)|X29!=k1_zfmisc_1(X28)))&((~r2_hidden(esk2_2(X32,X33),X33)|~r1_tarski(esk2_2(X32,X33),X32)|X33=k1_zfmisc_1(X32))&(r2_hidden(esk2_2(X32,X33),X33)|r1_tarski(esk2_2(X32,X33),X32)|X33=k1_zfmisc_1(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.47/0.67  fof(c_0_17, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3))))), inference(assume_negation,[status(cth)],[t32_subset_1])).
% 0.47/0.67  fof(c_0_18, plain, ![X41, X42]:m1_subset_1(k6_subset_1(X41,X42),k1_zfmisc_1(X41)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 0.47/0.67  fof(c_0_19, plain, ![X44, X45]:k6_subset_1(X44,X45)=k4_xboole_0(X44,X45), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.47/0.67  fof(c_0_20, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.47/0.67  fof(c_0_21, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k3_xboole_0(X18,X19)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.47/0.67  cnf(c_0_22, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.47/0.67  fof(c_0_23, plain, ![X37, X38]:(((~m1_subset_1(X38,X37)|r2_hidden(X38,X37)|v1_xboole_0(X37))&(~r2_hidden(X38,X37)|m1_subset_1(X38,X37)|v1_xboole_0(X37)))&((~m1_subset_1(X38,X37)|v1_xboole_0(X38)|~v1_xboole_0(X37))&(~v1_xboole_0(X38)|m1_subset_1(X38,X37)|~v1_xboole_0(X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.47/0.67  fof(c_0_24, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))&k7_subset_1(esk3_0,esk4_0,esk5_0)!=k9_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.47/0.67  fof(c_0_25, plain, ![X43]:~v1_xboole_0(k1_zfmisc_1(X43)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.47/0.67  cnf(c_0_26, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.67  cnf(c_0_27, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.67  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.67  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.67  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_22])).
% 0.47/0.67  cnf(c_0_31, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.47/0.67  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.47/0.67  cnf(c_0_33, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.47/0.67  fof(c_0_34, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.47/0.67  fof(c_0_35, plain, ![X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(X39))|k3_subset_1(X39,X40)=k4_xboole_0(X39,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.47/0.67  fof(c_0_36, plain, ![X46, X47, X48]:(~m1_subset_1(X47,k1_zfmisc_1(X46))|k7_subset_1(X46,X47,X48)=k4_xboole_0(X47,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.47/0.67  fof(c_0_37, plain, ![X22, X23, X24]:k3_xboole_0(X22,k4_xboole_0(X23,X24))=k4_xboole_0(k3_xboole_0(X22,X23),X24), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.47/0.67  fof(c_0_38, plain, ![X25, X26, X27]:k3_xboole_0(X25,k4_xboole_0(X26,X27))=k4_xboole_0(k3_xboole_0(X25,X26),k3_xboole_0(X25,X27)), inference(variable_rename,[status(thm)],[t50_xboole_1])).
% 0.47/0.67  cnf(c_0_39, plain, (m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.47/0.67  cnf(c_0_40, plain, (k3_xboole_0(X1,X2)=X1|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.47/0.67  cnf(c_0_41, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.47/0.67  cnf(c_0_42, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.47/0.67  cnf(c_0_43, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.47/0.67  cnf(c_0_44, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.47/0.67  fof(c_0_45, plain, ![X35, X36]:k1_zfmisc_1(k3_xboole_0(X35,X36))=k3_xboole_0(k1_zfmisc_1(X35),k1_zfmisc_1(X36)), inference(variable_rename,[status(thm)],[t83_zfmisc_1])).
% 0.47/0.67  cnf(c_0_46, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.47/0.67  cnf(c_0_47, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.47/0.67  fof(c_0_48, plain, ![X20, X21]:k4_xboole_0(X20,k4_xboole_0(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.47/0.67  cnf(c_0_49, plain, (r2_hidden(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_39]), c_0_33])).
% 0.47/0.67  cnf(c_0_50, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.47/0.67  cnf(c_0_51, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_43, c_0_28])).
% 0.47/0.67  cnf(c_0_52, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_44, c_0_28])).
% 0.47/0.67  cnf(c_0_53, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.47/0.67  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.47/0.67  cnf(c_0_55, plain, (k1_zfmisc_1(k3_xboole_0(X1,X2))=k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.47/0.67  cnf(c_0_56, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_28]), c_0_28])).
% 0.47/0.67  cnf(c_0_57, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_28]), c_0_28])).
% 0.47/0.67  cnf(c_0_58, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.47/0.67  cnf(c_0_59, negated_conjecture, (r2_hidden(k5_xboole_0(esk3_0,esk5_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.47/0.67  cnf(c_0_60, negated_conjecture, (k7_subset_1(esk3_0,esk4_0,esk5_0)!=k9_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.47/0.67  cnf(c_0_61, negated_conjecture, (k3_subset_1(esk3_0,esk5_0)=k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_51, c_0_32])).
% 0.47/0.67  cnf(c_0_62, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k3_xboole_0(X2,X3))|~r2_hidden(X2,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_33])).
% 0.47/0.67  cnf(c_0_63, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_54]), c_0_33])).
% 0.47/0.67  cnf(c_0_64, plain, (k3_subset_1(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~m1_subset_1(X3,k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_55]), c_0_56])).
% 0.47/0.67  cnf(c_0_65, plain, (m1_subset_1(k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))),k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_55]), c_0_56])).
% 0.47/0.67  cnf(c_0_66, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X1,X3))))=k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_57, c_0_56])).
% 0.47/0.67  cnf(c_0_67, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_28]), c_0_28])).
% 0.47/0.67  cnf(c_0_68, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk5_0))=k5_xboole_0(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_59]), c_0_42])).
% 0.47/0.67  cnf(c_0_69, negated_conjecture, (k9_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0)))!=k7_subset_1(esk3_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 0.47/0.67  cnf(c_0_70, negated_conjecture, (k7_subset_1(esk3_0,esk4_0,X1)=k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.47/0.67  fof(c_0_71, plain, ![X49, X50, X51]:(~m1_subset_1(X51,k1_zfmisc_1(X49))|k9_subset_1(X49,X50,X51)=k3_xboole_0(X50,X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.47/0.67  cnf(c_0_72, plain, (k3_subset_1(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_67])).
% 0.47/0.67  cnf(c_0_73, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk5_0))=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_50]), c_0_68])).
% 0.47/0.67  cnf(c_0_74, negated_conjecture, (k9_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0)))!=k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0))), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.47/0.67  cnf(c_0_75, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.47/0.67  cnf(c_0_76, negated_conjecture, (m1_subset_1(k5_xboole_0(esk3_0,esk5_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_39, c_0_50])).
% 0.47/0.67  cnf(c_0_77, negated_conjecture, (k3_subset_1(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk5_0))=k3_xboole_0(X1,k5_xboole_0(esk3_0,esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_68]), c_0_73])).
% 0.47/0.67  cnf(c_0_78, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_39, c_0_67])).
% 0.47/0.67  cnf(c_0_79, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_66]), c_0_67])).
% 0.47/0.67  cnf(c_0_80, negated_conjecture, (k9_subset_1(esk3_0,esk4_0,k5_xboole_0(esk3_0,esk5_0))!=k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0))), inference(rw,[status(thm)],[c_0_74, c_0_50])).
% 0.47/0.67  cnf(c_0_81, negated_conjecture, (k9_subset_1(esk3_0,X1,k5_xboole_0(esk3_0,esk5_0))=k3_xboole_0(X1,k5_xboole_0(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.47/0.67  cnf(c_0_82, negated_conjecture, (k3_subset_1(k3_xboole_0(esk3_0,X1),k3_xboole_0(X1,esk5_0))=k3_xboole_0(X1,k5_xboole_0(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_77, c_0_42])).
% 0.47/0.67  cnf(c_0_83, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_63]), c_0_42])).
% 0.47/0.67  cnf(c_0_84, plain, (k3_subset_1(X1,k3_xboole_0(X1,X2))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_78]), c_0_79])).
% 0.47/0.67  cnf(c_0_85, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0))!=k3_xboole_0(esk4_0,k5_xboole_0(esk3_0,esk5_0))), inference(rw,[status(thm)],[c_0_80, c_0_81])).
% 0.47/0.67  cnf(c_0_86, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_85]), ['proof']).
% 0.47/0.67  # SZS output end CNFRefutation
% 0.47/0.67  # Proof object total steps             : 87
% 0.47/0.67  # Proof object clause steps            : 54
% 0.47/0.67  # Proof object formula steps           : 33
% 0.47/0.67  # Proof object conjectures             : 24
% 0.47/0.67  # Proof object clause conjectures      : 21
% 0.47/0.67  # Proof object formula conjectures     : 3
% 0.47/0.67  # Proof object initial clauses used    : 19
% 0.47/0.67  # Proof object initial formulas used   : 16
% 0.47/0.67  # Proof object generating inferences   : 23
% 0.47/0.67  # Proof object simplifying inferences  : 33
% 0.47/0.67  # Training examples: 0 positive, 0 negative
% 0.47/0.67  # Parsed axioms                        : 17
% 0.47/0.67  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.67  # Initial clauses                      : 30
% 0.47/0.67  # Removed in clause preprocessing      : 2
% 0.47/0.67  # Initial clauses in saturation        : 28
% 0.47/0.67  # Processed clauses                    : 3135
% 0.47/0.67  # ...of these trivial                  : 898
% 0.47/0.67  # ...subsumed                          : 1046
% 0.47/0.67  # ...remaining for further processing  : 1191
% 0.47/0.67  # Other redundant clauses eliminated   : 5
% 0.47/0.67  # Clauses deleted for lack of memory   : 0
% 0.47/0.67  # Backward-subsumed                    : 0
% 0.47/0.67  # Backward-rewritten                   : 164
% 0.47/0.67  # Generated clauses                    : 36338
% 0.47/0.67  # ...of the previous two non-trivial   : 25957
% 0.47/0.67  # Contextual simplify-reflections      : 0
% 0.47/0.67  # Paramodulations                      : 36263
% 0.47/0.67  # Factorizations                       : 70
% 0.47/0.67  # Equation resolutions                 : 5
% 0.47/0.67  # Propositional unsat checks           : 0
% 0.47/0.67  #    Propositional check models        : 0
% 0.47/0.67  #    Propositional check unsatisfiable : 0
% 0.47/0.67  #    Propositional clauses             : 0
% 0.47/0.67  #    Propositional clauses after purity: 0
% 0.47/0.67  #    Propositional unsat core size     : 0
% 0.47/0.67  #    Propositional preprocessing time  : 0.000
% 0.47/0.67  #    Propositional encoding time       : 0.000
% 0.47/0.67  #    Propositional solver time         : 0.000
% 0.47/0.67  #    Success case prop preproc time    : 0.000
% 0.47/0.67  #    Success case prop encoding time   : 0.000
% 0.47/0.67  #    Success case prop solver time     : 0.000
% 0.47/0.67  # Current number of processed clauses  : 994
% 0.47/0.67  #    Positive orientable unit clauses  : 692
% 0.47/0.67  #    Positive unorientable unit clauses: 5
% 0.47/0.67  #    Negative unit clauses             : 4
% 0.47/0.67  #    Non-unit-clauses                  : 293
% 0.47/0.67  # Current number of unprocessed clauses: 22480
% 0.47/0.67  # ...number of literals in the above   : 45453
% 0.47/0.67  # Current number of archived formulas  : 0
% 0.47/0.67  # Current number of archived clauses   : 194
% 0.47/0.67  # Clause-clause subsumption calls (NU) : 12613
% 0.47/0.67  # Rec. Clause-clause subsumption calls : 10293
% 0.47/0.67  # Non-unit clause-clause subsumptions  : 729
% 0.47/0.67  # Unit Clause-clause subsumption calls : 1624
% 0.47/0.67  # Rewrite failures with RHS unbound    : 0
% 0.47/0.67  # BW rewrite match attempts            : 3462
% 0.47/0.67  # BW rewrite match successes           : 319
% 0.47/0.67  # Condensation attempts                : 0
% 0.47/0.67  # Condensation successes               : 0
% 0.47/0.67  # Termbank termtop insertions          : 573731
% 0.47/0.67  
% 0.47/0.67  # -------------------------------------------------
% 0.47/0.67  # User time                : 0.316 s
% 0.47/0.67  # System time              : 0.018 s
% 0.47/0.67  # Total time               : 0.335 s
% 0.47/0.67  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
