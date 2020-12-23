%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:52 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  117 (1659 expanded)
%              Number of clauses        :   88 ( 794 expanded)
%              Number of leaves         :   14 ( 429 expanded)
%              Depth                    :   21
%              Number of atoms          :  272 (3657 expanded)
%              Number of equality atoms :   76 (1431 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t38_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(c_0_14,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k4_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_15,plain,(
    ! [X24,X25] : k4_xboole_0(X24,X25) = k5_xboole_0(X24,k3_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_16,plain,(
    ! [X22,X23] :
      ( ( ~ r1_xboole_0(X22,X23)
        | k3_xboole_0(X22,X23) = k1_xboole_0 )
      & ( k3_xboole_0(X22,X23) != k1_xboole_0
        | r1_xboole_0(X22,X23) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_17,plain,(
    ! [X30] : r1_xboole_0(X30,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_18,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,X29)) = k3_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_19,plain,(
    ! [X31,X32,X33,X34,X35,X36] :
      ( ( ~ r2_hidden(X33,X32)
        | r1_tarski(X33,X31)
        | X32 != k1_zfmisc_1(X31) )
      & ( ~ r1_tarski(X34,X31)
        | r2_hidden(X34,X32)
        | X32 != k1_zfmisc_1(X31) )
      & ( ~ r2_hidden(esk3_2(X35,X36),X36)
        | ~ r1_tarski(esk3_2(X35,X36),X35)
        | X36 = k1_zfmisc_1(X35) )
      & ( r2_hidden(esk3_2(X35,X36),X36)
        | r1_tarski(esk3_2(X35,X36),X35)
        | X36 = k1_zfmisc_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X26,X27] :
      ( ~ r1_tarski(X26,X27)
      | k3_xboole_0(X26,X27) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_29,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_21]),c_0_21])).

fof(c_0_33,plain,(
    ! [X38,X39] :
      ( ( ~ m1_subset_1(X39,X38)
        | r2_hidden(X39,X38)
        | v1_xboole_0(X38) )
      & ( ~ r2_hidden(X39,X38)
        | m1_subset_1(X39,X38)
        | v1_xboole_0(X38) )
      & ( ~ m1_subset_1(X39,X38)
        | v1_xboole_0(X39)
        | ~ v1_xboole_0(X38) )
      & ( ~ v1_xboole_0(X39)
        | m1_subset_1(X39,X38)
        | ~ v1_xboole_0(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_30])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_30])).

cnf(c_0_42,plain,
    ( r1_tarski(esk1_2(k1_zfmisc_1(X1),X2),X1)
    | r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_43,plain,(
    ! [X43] : ~ v1_xboole_0(k1_zfmisc_1(X43)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_xboole_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_30])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_38]),c_0_38])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_39]),c_0_30])).

cnf(c_0_48,plain,
    ( m1_subset_1(esk1_2(X1,X2),X1)
    | v1_xboole_0(X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_36])).

cnf(c_0_49,plain,
    ( esk1_2(k1_zfmisc_1(k1_xboole_0),X1) = k1_xboole_0
    | r1_tarski(k1_zfmisc_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_54,plain,(
    ! [X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X41))
      | k3_subset_1(X41,X42) = k4_xboole_0(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1
    | ~ r1_tarski(X1,k5_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_47])).

cnf(c_0_56,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_zfmisc_1(k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_57,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(esk1_2(X1,k1_zfmisc_1(X2)),X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_36])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_32])).

cnf(c_0_61,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,plain,
    ( k5_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(X3),X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_52])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_49]),c_0_59])])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X2,k3_xboole_0(X2,X3))))
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_32])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

cnf(c_0_67,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_61,c_0_21])).

cnf(c_0_68,plain,
    ( k3_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_62])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,plain,
    ( k5_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = k3_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_69]),c_0_50])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X3,k5_xboole_0(X3,X2))
    | ~ r1_tarski(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_34]),c_0_57])).

cnf(c_0_74,plain,
    ( k5_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = k3_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_56])).

cnf(c_0_75,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_64])]),c_0_56])).

cnf(c_0_76,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_52])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_79,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_59])).

cnf(c_0_80,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_81,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(X2,k3_subset_1(X1,X2))
        <=> X2 = k1_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t38_subset_1])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_77,c_0_21])).

cnf(c_0_83,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_50])).

cnf(c_0_84,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_80,c_0_21])).

fof(c_0_85,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))
    & ( ~ r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))
      | esk5_0 != k1_subset_1(esk4_0) )
    & ( r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))
      | esk5_0 = k1_subset_1(esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_81])])])).

fof(c_0_86,plain,(
    ! [X40] : k1_subset_1(X40) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_82])).

cnf(c_0_88,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2))
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_34])).

cnf(c_0_89,plain,
    ( r2_hidden(k1_xboole_0,X1)
    | ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_83])).

cnf(c_0_90,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_52]),c_0_50])).

cnf(c_0_91,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_84]),c_0_38]),c_0_46])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))
    | esk5_0 = k1_subset_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_93,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_95,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2))
    | ~ r1_tarski(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_34]),c_0_88])).

cnf(c_0_96,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_64])).

cnf(c_0_97,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_66])).

cnf(c_0_98,plain,
    ( k5_xboole_0(X1,X2) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_66]),c_0_90])).

cnf(c_0_99,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_91])).

cnf(c_0_100,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_94]),c_0_50])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_95,c_0_91])).

cnf(c_0_103,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_36])).

cnf(c_0_104,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = k3_subset_1(X1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_30])).

cnf(c_0_105,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_96]),c_0_50])).

cnf(c_0_106,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))
    | esk5_0 != k1_subset_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_107,plain,
    ( ~ r2_hidden(X1,k3_subset_1(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_108,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,X1,esk5_0),k3_subset_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_101])).

cnf(c_0_110,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X2))) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_66])).

cnf(c_0_111,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_112,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = k3_subset_1(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_105])])).

cnf(c_0_113,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | ~ r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_106,c_0_93])).

cnf(c_0_114,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109])]),c_0_91])).

cnf(c_0_115,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_30]),c_0_112]),c_0_103])])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_114]),c_0_114]),c_0_114]),c_0_115]),c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.59/0.77  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.59/0.77  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.59/0.77  #
% 0.59/0.77  # Preprocessing time       : 0.027 s
% 0.59/0.77  # Presaturation interreduction done
% 0.59/0.77  
% 0.59/0.77  # Proof found!
% 0.59/0.77  # SZS status Theorem
% 0.59/0.77  # SZS output start CNFRefutation
% 0.59/0.77  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.59/0.77  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.59/0.77  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.59/0.77  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.59/0.77  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.59/0.77  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.59/0.77  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.59/0.77  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.59/0.77  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.59/0.77  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.59/0.77  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.59/0.77  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.59/0.77  fof(t38_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 0.59/0.77  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.59/0.77  fof(c_0_14, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k4_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k4_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.59/0.77  fof(c_0_15, plain, ![X24, X25]:k4_xboole_0(X24,X25)=k5_xboole_0(X24,k3_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.59/0.77  fof(c_0_16, plain, ![X22, X23]:((~r1_xboole_0(X22,X23)|k3_xboole_0(X22,X23)=k1_xboole_0)&(k3_xboole_0(X22,X23)!=k1_xboole_0|r1_xboole_0(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.59/0.77  fof(c_0_17, plain, ![X30]:r1_xboole_0(X30,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.59/0.77  fof(c_0_18, plain, ![X28, X29]:k4_xboole_0(X28,k4_xboole_0(X28,X29))=k3_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.59/0.77  fof(c_0_19, plain, ![X31, X32, X33, X34, X35, X36]:(((~r2_hidden(X33,X32)|r1_tarski(X33,X31)|X32!=k1_zfmisc_1(X31))&(~r1_tarski(X34,X31)|r2_hidden(X34,X32)|X32!=k1_zfmisc_1(X31)))&((~r2_hidden(esk3_2(X35,X36),X36)|~r1_tarski(esk3_2(X35,X36),X35)|X36=k1_zfmisc_1(X35))&(r2_hidden(esk3_2(X35,X36),X36)|r1_tarski(esk3_2(X35,X36),X35)|X36=k1_zfmisc_1(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.59/0.77  cnf(c_0_20, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.59/0.77  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.59/0.77  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.59/0.77  cnf(c_0_23, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.59/0.77  fof(c_0_24, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.59/0.77  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.59/0.77  fof(c_0_26, plain, ![X26, X27]:(~r1_tarski(X26,X27)|k3_xboole_0(X26,X27)=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.59/0.77  cnf(c_0_27, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.59/0.77  fof(c_0_28, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.59/0.77  cnf(c_0_29, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.59/0.77  cnf(c_0_30, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.59/0.77  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.59/0.77  cnf(c_0_32, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_21]), c_0_21])).
% 0.59/0.77  fof(c_0_33, plain, ![X38, X39]:(((~m1_subset_1(X39,X38)|r2_hidden(X39,X38)|v1_xboole_0(X38))&(~r2_hidden(X39,X38)|m1_subset_1(X39,X38)|v1_xboole_0(X38)))&((~m1_subset_1(X39,X38)|v1_xboole_0(X39)|~v1_xboole_0(X38))&(~v1_xboole_0(X39)|m1_subset_1(X39,X38)|~v1_xboole_0(X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.59/0.77  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.59/0.77  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_27])).
% 0.59/0.77  cnf(c_0_36, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.59/0.77  cnf(c_0_37, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_29])).
% 0.59/0.77  cnf(c_0_38, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.59/0.77  cnf(c_0_39, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_30])).
% 0.59/0.77  cnf(c_0_40, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.59/0.77  cnf(c_0_41, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_30])).
% 0.59/0.77  cnf(c_0_42, plain, (r1_tarski(esk1_2(k1_zfmisc_1(X1),X2),X1)|r1_tarski(k1_zfmisc_1(X1),X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.59/0.77  fof(c_0_43, plain, ![X43]:~v1_xboole_0(k1_zfmisc_1(X43)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.59/0.77  cnf(c_0_44, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.59/0.77  cnf(c_0_45, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_xboole_0))|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_30])).
% 0.59/0.77  cnf(c_0_46, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_38]), c_0_38])).
% 0.59/0.77  cnf(c_0_47, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0))=k5_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_39]), c_0_30])).
% 0.59/0.77  cnf(c_0_48, plain, (m1_subset_1(esk1_2(X1,X2),X1)|v1_xboole_0(X1)|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_36])).
% 0.59/0.77  cnf(c_0_49, plain, (esk1_2(k1_zfmisc_1(k1_xboole_0),X1)=k1_xboole_0|r1_tarski(k1_zfmisc_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.59/0.77  cnf(c_0_50, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.59/0.77  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.59/0.77  cnf(c_0_52, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_44])).
% 0.59/0.77  cnf(c_0_53, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.59/0.77  fof(c_0_54, plain, ![X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(X41))|k3_subset_1(X41,X42)=k4_xboole_0(X41,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.59/0.77  cnf(c_0_55, plain, (k5_xboole_0(X1,k1_xboole_0)=X1|~r1_tarski(X1,k5_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_34, c_0_47])).
% 0.59/0.77  cnf(c_0_56, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))|r1_tarski(k1_zfmisc_1(k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.59/0.77  cnf(c_0_57, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.59/0.77  cnf(c_0_58, plain, (r1_tarski(X1,k1_zfmisc_1(X2))|~r1_tarski(esk1_2(X1,k1_zfmisc_1(X2)),X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.59/0.77  cnf(c_0_59, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_53, c_0_36])).
% 0.59/0.77  cnf(c_0_60, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_37, c_0_32])).
% 0.59/0.77  cnf(c_0_61, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.59/0.77  cnf(c_0_62, plain, (k5_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.59/0.77  cnf(c_0_63, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_zfmisc_1(X3),X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_57, c_0_52])).
% 0.59/0.77  cnf(c_0_64, plain, (r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_49]), c_0_59])])).
% 0.59/0.77  cnf(c_0_65, plain, (~r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X2,k3_xboole_0(X2,X3))))|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_60, c_0_32])).
% 0.59/0.77  cnf(c_0_66, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_31])).
% 0.59/0.77  cnf(c_0_67, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_61, c_0_21])).
% 0.59/0.77  cnf(c_0_68, plain, (k3_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))=k1_zfmisc_1(k1_xboole_0)|m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_47, c_0_62])).
% 0.59/0.77  cnf(c_0_69, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.59/0.77  cnf(c_0_70, plain, (~r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X2,X3)))|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.59/0.77  cnf(c_0_71, plain, (k5_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))=k3_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))|m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.59/0.77  cnf(c_0_72, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_69]), c_0_50])).
% 0.59/0.77  cnf(c_0_73, plain, (~r2_hidden(X1,X2)|~r1_tarski(X3,k5_xboole_0(X3,X2))|~r1_tarski(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_34]), c_0_57])).
% 0.59/0.77  cnf(c_0_74, plain, (k5_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))=k3_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))|m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_56])).
% 0.59/0.77  cnf(c_0_75, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))|~r2_hidden(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_64])]), c_0_56])).
% 0.59/0.77  cnf(c_0_76, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_75, c_0_52])).
% 0.59/0.77  cnf(c_0_77, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.59/0.77  cnf(c_0_78, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.59/0.77  cnf(c_0_79, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_76, c_0_59])).
% 0.59/0.77  cnf(c_0_80, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.59/0.77  fof(c_0_81, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1)))), inference(assume_negation,[status(cth)],[t38_subset_1])).
% 0.59/0.77  cnf(c_0_82, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_77, c_0_21])).
% 0.59/0.77  cnf(c_0_83, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_50])).
% 0.59/0.77  cnf(c_0_84, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_80, c_0_21])).
% 0.59/0.77  fof(c_0_85, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))&((~r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))|esk5_0!=k1_subset_1(esk4_0))&(r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))|esk5_0=k1_subset_1(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_81])])])).
% 0.59/0.77  fof(c_0_86, plain, ![X40]:k1_subset_1(X40)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.59/0.77  cnf(c_0_87, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_82])).
% 0.59/0.77  cnf(c_0_88, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))|~r2_hidden(X1,X2)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_60, c_0_34])).
% 0.59/0.77  cnf(c_0_89, plain, (r2_hidden(k1_xboole_0,X1)|~r1_tarski(k1_zfmisc_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_57, c_0_83])).
% 0.59/0.77  cnf(c_0_90, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_52]), c_0_50])).
% 0.59/0.77  cnf(c_0_91, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_84]), c_0_38]), c_0_46])).
% 0.59/0.77  cnf(c_0_92, negated_conjecture, (r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))|esk5_0=k1_subset_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.59/0.77  cnf(c_0_93, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.59/0.77  cnf(c_0_94, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.59/0.77  cnf(c_0_95, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))|~r1_tarski(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_34]), c_0_88])).
% 0.59/0.77  cnf(c_0_96, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_89, c_0_64])).
% 0.59/0.77  cnf(c_0_97, plain, (~r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_37, c_0_66])).
% 0.59/0.77  cnf(c_0_98, plain, (k5_xboole_0(X1,X2)=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_66]), c_0_90])).
% 0.59/0.77  cnf(c_0_99, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_57, c_0_91])).
% 0.59/0.77  cnf(c_0_100, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))), inference(rw,[status(thm)],[c_0_92, c_0_93])).
% 0.59/0.77  cnf(c_0_101, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_94]), c_0_50])).
% 0.59/0.77  cnf(c_0_102, plain, (k5_xboole_0(X1,X1)=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_95, c_0_91])).
% 0.59/0.77  cnf(c_0_103, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_51, c_0_36])).
% 0.59/0.77  cnf(c_0_104, plain, (k5_xboole_0(X1,k1_xboole_0)=k3_subset_1(X1,k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_67, c_0_30])).
% 0.59/0.77  cnf(c_0_105, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_96]), c_0_50])).
% 0.59/0.77  cnf(c_0_106, negated_conjecture, (~r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))|esk5_0!=k1_subset_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.59/0.77  cnf(c_0_107, plain, (~r2_hidden(X1,k3_subset_1(X2,X3))|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.59/0.77  cnf(c_0_108, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,X1,esk5_0),k3_subset_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.59/0.77  cnf(c_0_109, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_101])).
% 0.59/0.77  cnf(c_0_110, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X2)))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_32, c_0_66])).
% 0.59/0.77  cnf(c_0_111, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.59/0.77  cnf(c_0_112, plain, (k5_xboole_0(X1,k1_xboole_0)=k3_subset_1(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_105])])).
% 0.59/0.77  cnf(c_0_113, negated_conjecture, (esk5_0!=k1_xboole_0|~r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))), inference(rw,[status(thm)],[c_0_106, c_0_93])).
% 0.59/0.77  cnf(c_0_114, negated_conjecture, (esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109])]), c_0_91])).
% 0.59/0.77  cnf(c_0_115, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_30]), c_0_112]), c_0_103])])).
% 0.59/0.77  cnf(c_0_116, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_114]), c_0_114]), c_0_114]), c_0_115]), c_0_59])]), ['proof']).
% 0.59/0.77  # SZS output end CNFRefutation
% 0.59/0.77  # Proof object total steps             : 117
% 0.59/0.77  # Proof object clause steps            : 88
% 0.59/0.77  # Proof object formula steps           : 29
% 0.59/0.77  # Proof object conjectures             : 13
% 0.59/0.77  # Proof object clause conjectures      : 10
% 0.59/0.77  # Proof object formula conjectures     : 3
% 0.59/0.77  # Proof object initial clauses used    : 22
% 0.59/0.77  # Proof object initial formulas used   : 14
% 0.59/0.77  # Proof object generating inferences   : 53
% 0.59/0.77  # Proof object simplifying inferences  : 46
% 0.59/0.77  # Training examples: 0 positive, 0 negative
% 0.59/0.77  # Parsed axioms                        : 14
% 0.59/0.77  # Removed by relevancy pruning/SinE    : 0
% 0.59/0.77  # Initial clauses                      : 30
% 0.59/0.77  # Removed in clause preprocessing      : 2
% 0.59/0.77  # Initial clauses in saturation        : 28
% 0.59/0.77  # Processed clauses                    : 2490
% 0.59/0.77  # ...of these trivial                  : 18
% 0.59/0.77  # ...subsumed                          : 1945
% 0.59/0.77  # ...remaining for further processing  : 527
% 0.59/0.77  # Other redundant clauses eliminated   : 6
% 0.59/0.77  # Clauses deleted for lack of memory   : 0
% 0.59/0.77  # Backward-subsumed                    : 42
% 0.59/0.77  # Backward-rewritten                   : 106
% 0.59/0.77  # Generated clauses                    : 28098
% 0.59/0.77  # ...of the previous two non-trivial   : 26699
% 0.59/0.77  # Contextual simplify-reflections      : 11
% 0.59/0.77  # Paramodulations                      : 27947
% 0.59/0.77  # Factorizations                       : 145
% 0.59/0.77  # Equation resolutions                 : 6
% 0.59/0.77  # Propositional unsat checks           : 0
% 0.59/0.77  #    Propositional check models        : 0
% 0.59/0.77  #    Propositional check unsatisfiable : 0
% 0.59/0.77  #    Propositional clauses             : 0
% 0.59/0.77  #    Propositional clauses after purity: 0
% 0.59/0.77  #    Propositional unsat core size     : 0
% 0.59/0.77  #    Propositional preprocessing time  : 0.000
% 0.59/0.77  #    Propositional encoding time       : 0.000
% 0.59/0.77  #    Propositional solver time         : 0.000
% 0.59/0.77  #    Success case prop preproc time    : 0.000
% 0.59/0.77  #    Success case prop encoding time   : 0.000
% 0.59/0.77  #    Success case prop solver time     : 0.000
% 0.59/0.77  # Current number of processed clauses  : 346
% 0.59/0.77  #    Positive orientable unit clauses  : 24
% 0.59/0.77  #    Positive unorientable unit clauses: 1
% 0.59/0.77  #    Negative unit clauses             : 2
% 0.59/0.77  #    Non-unit-clauses                  : 319
% 0.59/0.77  # Current number of unprocessed clauses: 23897
% 0.59/0.77  # ...number of literals in the above   : 112641
% 0.59/0.77  # Current number of archived formulas  : 0
% 0.59/0.77  # Current number of archived clauses   : 178
% 0.59/0.77  # Clause-clause subsumption calls (NU) : 23370
% 0.59/0.77  # Rec. Clause-clause subsumption calls : 12574
% 0.59/0.77  # Non-unit clause-clause subsumptions  : 1158
% 0.59/0.77  # Unit Clause-clause subsumption calls : 992
% 0.59/0.77  # Rewrite failures with RHS unbound    : 0
% 0.59/0.77  # BW rewrite match attempts            : 131
% 0.59/0.77  # BW rewrite match successes           : 55
% 0.59/0.77  # Condensation attempts                : 0
% 0.59/0.77  # Condensation successes               : 0
% 0.59/0.77  # Termbank termtop insertions          : 519048
% 0.59/0.77  
% 0.59/0.77  # -------------------------------------------------
% 0.59/0.77  # User time                : 0.414 s
% 0.59/0.77  # System time              : 0.012 s
% 0.59/0.77  # Total time               : 0.427 s
% 0.59/0.77  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
