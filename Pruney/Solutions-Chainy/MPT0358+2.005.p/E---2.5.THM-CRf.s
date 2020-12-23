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
% DateTime   : Thu Dec  3 10:45:51 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 (1407 expanded)
%              Number of clauses        :   63 ( 626 expanded)
%              Number of leaves         :   17 ( 387 expanded)
%              Depth                    :   15
%              Number of atoms          :  209 (2467 expanded)
%              Number of equality atoms :   83 (1314 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t38_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_17,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_18,plain,(
    ! [X25,X26] : k4_xboole_0(X25,X26) = k5_xboole_0(X25,k3_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_19,plain,(
    ! [X40,X41] : k3_xboole_0(X40,X41) = k5_xboole_0(k5_xboole_0(X40,X41),k2_xboole_0(X40,X41)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

fof(c_0_20,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X36,X37,X38] : k5_xboole_0(k5_xboole_0(X36,X37),X38) = k5_xboole_0(X36,k5_xboole_0(X37,X38)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( X3 != k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X4,X2),k2_xboole_0(X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_27,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_23]),c_0_23])).

fof(c_0_29,plain,(
    ! [X39] : k5_xboole_0(X39,X39) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_30,plain,(
    ! [X54,X55] :
      ( ~ m1_subset_1(X55,k1_zfmisc_1(X54))
      | k3_subset_1(X54,X55) = k4_xboole_0(X54,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(X2,k3_subset_1(X1,X2))
        <=> X2 = k1_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t38_subset_1])).

cnf(c_0_32,plain,
    ( X1 != k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))))
    | ~ r2_hidden(X4,X1)
    | ~ r2_hidden(X4,X3) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_27]),c_0_27])).

fof(c_0_34,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | k2_xboole_0(X27,X28) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_35,plain,(
    ! [X35] : k5_xboole_0(X35,k1_xboole_0) = X35 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_38,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))
    & ( ~ r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
      | esk6_0 != k1_subset_1(esk5_0) )
    & ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
      | esk6_0 = k1_subset_1(esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

fof(c_0_39,plain,(
    ! [X53] : k1_subset_1(X53) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_40,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_41,plain,(
    ! [X32] : k3_xboole_0(X32,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_42,plain,(
    ! [X34] :
      ( ~ r1_tarski(X34,k1_xboole_0)
      | X34 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_43,plain,(
    ! [X49,X50] :
      ( ( ~ r1_tarski(k1_tarski(X49),X50)
        | r2_hidden(X49,X50) )
      & ( ~ r2_hidden(X49,X50)
        | r1_tarski(k1_tarski(X49),X50) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_44,plain,
    ( X1 != k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,k2_xboole_0(X3,X2))))
    | ~ r2_hidden(X4,X1)
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_47,plain,(
    ! [X33] : r1_tarski(k1_xboole_0,X33) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_36])).

cnf(c_0_49,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_22]),c_0_23])).

fof(c_0_50,plain,(
    ! [X29,X30,X31] :
      ( ~ r1_tarski(X29,X30)
      | ~ r1_tarski(X30,X31)
      | r1_tarski(X29,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
    | esk6_0 = k1_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_53,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_54,plain,
    ( X3 = k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_22]),c_0_23])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,plain,
    ( X1 != k5_xboole_0(X2,X3)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X4,X1)
    | ~ r2_hidden(X4,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_36]),c_0_46])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,plain,
    ( X1 != k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k2_xboole_0(X3,X2)))
    | ~ r2_hidden(X4,X1)
    | ~ r2_hidden(X4,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_48])).

cnf(c_0_61,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_36]),c_0_46])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_27])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_65,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_66,plain,
    ( X1 = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))))
    | r2_hidden(esk2_3(X2,X3,X1),X2)
    | r2_hidden(esk2_3(X2,X3,X1),X1) ),
    inference(rw,[status(thm)],[c_0_54,c_0_27])).

cnf(c_0_67,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_55,c_0_23])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_69,plain,
    ( k1_tarski(X1) = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_46]),c_0_59])])])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_72,plain,
    ( X1 != k5_xboole_0(X2,k2_xboole_0(X3,X2))
    | ~ r2_hidden(X4,X1)
    | ~ r2_hidden(X4,X2) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X2,X1)) = k3_subset_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_48]),c_0_61])).

cnf(c_0_74,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(X1,k3_subset_1(esk5_0,esk6_0))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_75,plain,
    ( X1 = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))))
    | r2_hidden(esk2_3(X2,X3,X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_67,c_0_46])).

cnf(c_0_77,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_59])]),c_0_70])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X4),k2_xboole_0(X2,X4)))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_22]),c_0_23])).

cnf(c_0_79,plain,
    ( X1 != k3_subset_1(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X4,X1)
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_81,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(k1_tarski(X1),k3_subset_1(esk5_0,esk6_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_57])).

cnf(c_0_82,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_83,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_46]),c_0_46]),c_0_77])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X4,k2_xboole_0(X2,X4))))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_78,c_0_27])).

cnf(c_0_85,negated_conjecture,
    ( X1 != k3_subset_1(esk5_0,esk6_0)
    | ~ r2_hidden(X2,esk6_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(k1_tarski(esk1_1(esk6_0)),k3_subset_1(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X4,k2_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_48]),c_0_61])).

cnf(c_0_88,plain,
    ( k5_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_61]),c_0_61]),c_0_76])).

cnf(c_0_89,negated_conjecture,
    ( ~ r2_hidden(X1,k3_subset_1(esk5_0,esk6_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(er,[status(thm)],[c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk1_1(esk6_0),k3_subset_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_86])).

cnf(c_0_91,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_77])).

cnf(c_0_92,negated_conjecture,
    ( ~ r2_hidden(esk1_1(esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])).

cnf(c_0_93,negated_conjecture,
    ( ~ r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
    | esk6_0 != k1_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_94,negated_conjecture,
    ( v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_82])).

cnf(c_0_95,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_93,c_0_52])).

cnf(c_0_96,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96]),c_0_96]),c_0_96]),c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:37:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.46  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.21/0.46  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.21/0.46  #
% 0.21/0.46  # Preprocessing time       : 0.029 s
% 0.21/0.46  
% 0.21/0.46  # Proof found!
% 0.21/0.46  # SZS status Theorem
% 0.21/0.46  # SZS output start CNFRefutation
% 0.21/0.46  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.21/0.46  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.46  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.21/0.46  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.46  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.21/0.46  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.21/0.46  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.21/0.46  fof(t38_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 0.21/0.46  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.21/0.46  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.21/0.46  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 0.21/0.46  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.21/0.46  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.21/0.46  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.21/0.46  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.46  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.21/0.46  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.46  fof(c_0_17, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.21/0.46  fof(c_0_18, plain, ![X25, X26]:k4_xboole_0(X25,X26)=k5_xboole_0(X25,k3_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.46  fof(c_0_19, plain, ![X40, X41]:k3_xboole_0(X40,X41)=k5_xboole_0(k5_xboole_0(X40,X41),k2_xboole_0(X40,X41)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.21/0.46  fof(c_0_20, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.46  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.46  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.46  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.46  fof(c_0_24, plain, ![X36, X37, X38]:k5_xboole_0(k5_xboole_0(X36,X37),X38)=k5_xboole_0(X36,k5_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.21/0.46  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.46  cnf(c_0_26, plain, (X3!=k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X4,X2),k2_xboole_0(X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.21/0.46  cnf(c_0_27, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.46  cnf(c_0_28, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_23]), c_0_23])).
% 0.21/0.46  fof(c_0_29, plain, ![X39]:k5_xboole_0(X39,X39)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.21/0.46  fof(c_0_30, plain, ![X54, X55]:(~m1_subset_1(X55,k1_zfmisc_1(X54))|k3_subset_1(X54,X55)=k4_xboole_0(X54,X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.21/0.46  fof(c_0_31, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1)))), inference(assume_negation,[status(cth)],[t38_subset_1])).
% 0.21/0.46  cnf(c_0_32, plain, (X1!=k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))))|~r2_hidden(X4,X1)|~r2_hidden(X4,X3)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.46  cnf(c_0_33, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))=k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_27]), c_0_27])).
% 0.21/0.46  fof(c_0_34, plain, ![X27, X28]:(~r1_tarski(X27,X28)|k2_xboole_0(X27,X28)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.21/0.46  fof(c_0_35, plain, ![X35]:k5_xboole_0(X35,k1_xboole_0)=X35, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.21/0.46  cnf(c_0_36, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.46  cnf(c_0_37, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.46  fof(c_0_38, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))&((~r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0!=k1_subset_1(esk5_0))&(r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0=k1_subset_1(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.21/0.46  fof(c_0_39, plain, ![X53]:k1_subset_1(X53)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.21/0.46  cnf(c_0_40, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.46  fof(c_0_41, plain, ![X32]:k3_xboole_0(X32,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.21/0.46  fof(c_0_42, plain, ![X34]:(~r1_tarski(X34,k1_xboole_0)|X34=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.21/0.46  fof(c_0_43, plain, ![X49, X50]:((~r1_tarski(k1_tarski(X49),X50)|r2_hidden(X49,X50))&(~r2_hidden(X49,X50)|r1_tarski(k1_tarski(X49),X50))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.21/0.46  cnf(c_0_44, plain, (X1!=k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,k2_xboole_0(X3,X2))))|~r2_hidden(X4,X1)|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.46  cnf(c_0_45, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.46  cnf(c_0_46, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.46  fof(c_0_47, plain, ![X33]:r1_tarski(k1_xboole_0,X33), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.46  cnf(c_0_48, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_27, c_0_36])).
% 0.21/0.46  cnf(c_0_49, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_22]), c_0_23])).
% 0.21/0.46  fof(c_0_50, plain, ![X29, X30, X31]:(~r1_tarski(X29,X30)|~r1_tarski(X30,X31)|r1_tarski(X29,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.21/0.46  cnf(c_0_51, negated_conjecture, (r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0=k1_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.46  cnf(c_0_52, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.46  fof(c_0_53, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.46  cnf(c_0_54, plain, (X3=k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_22]), c_0_23])).
% 0.21/0.46  cnf(c_0_55, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.46  cnf(c_0_56, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.46  cnf(c_0_57, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.46  cnf(c_0_58, plain, (X1!=k5_xboole_0(X2,X3)|~r1_tarski(X3,X2)|~r2_hidden(X4,X1)|~r2_hidden(X4,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_36]), c_0_46])).
% 0.21/0.46  cnf(c_0_59, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.46  cnf(c_0_60, plain, (X1!=k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k2_xboole_0(X3,X2)))|~r2_hidden(X4,X1)|~r2_hidden(X4,X2)), inference(rw,[status(thm)],[c_0_32, c_0_48])).
% 0.21/0.46  cnf(c_0_61, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_36]), c_0_46])).
% 0.21/0.46  cnf(c_0_62, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_49, c_0_27])).
% 0.21/0.46  cnf(c_0_63, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.46  cnf(c_0_64, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.46  cnf(c_0_65, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.46  cnf(c_0_66, plain, (X1=k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))))|r2_hidden(esk2_3(X2,X3,X1),X2)|r2_hidden(esk2_3(X2,X3,X1),X1)), inference(rw,[status(thm)],[c_0_54, c_0_27])).
% 0.21/0.46  cnf(c_0_67, plain, (k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_55, c_0_23])).
% 0.21/0.46  cnf(c_0_68, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.46  cnf(c_0_69, plain, (k1_tarski(X1)=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.46  cnf(c_0_70, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_46]), c_0_59])])])).
% 0.21/0.46  cnf(c_0_71, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.46  cnf(c_0_72, plain, (X1!=k5_xboole_0(X2,k2_xboole_0(X3,X2))|~r2_hidden(X4,X1)|~r2_hidden(X4,X2)), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 0.21/0.46  cnf(c_0_73, plain, (k5_xboole_0(X1,k2_xboole_0(X2,X1))=k3_subset_1(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_48]), c_0_61])).
% 0.21/0.46  cnf(c_0_74, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(X1,k3_subset_1(esk5_0,esk6_0))|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.21/0.46  cnf(c_0_75, plain, (X1=k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))))|r2_hidden(esk2_3(X2,X3,X1),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.21/0.46  cnf(c_0_76, plain, (k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_67, c_0_46])).
% 0.21/0.46  cnf(c_0_77, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_59])]), c_0_70])).
% 0.21/0.46  cnf(c_0_78, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X4),k2_xboole_0(X2,X4)))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_22]), c_0_23])).
% 0.21/0.46  cnf(c_0_79, plain, (X1!=k3_subset_1(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X4,X1)|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.21/0.46  cnf(c_0_80, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.46  cnf(c_0_81, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(k1_tarski(X1),k3_subset_1(esk5_0,esk6_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_74, c_0_57])).
% 0.21/0.46  cnf(c_0_82, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.46  cnf(c_0_83, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_46]), c_0_46]), c_0_77])).
% 0.21/0.46  cnf(c_0_84, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X4,k2_xboole_0(X2,X4))))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_78, c_0_27])).
% 0.21/0.46  cnf(c_0_85, negated_conjecture, (X1!=k3_subset_1(esk5_0,esk6_0)|~r2_hidden(X2,esk6_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.21/0.46  cnf(c_0_86, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(k1_tarski(esk1_1(esk6_0)),k3_subset_1(esk5_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])).
% 0.21/0.46  cnf(c_0_87, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X4,k2_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_48]), c_0_61])).
% 0.21/0.46  cnf(c_0_88, plain, (k5_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_61]), c_0_61]), c_0_76])).
% 0.21/0.46  cnf(c_0_89, negated_conjecture, (~r2_hidden(X1,k3_subset_1(esk5_0,esk6_0))|~r2_hidden(X1,esk6_0)), inference(er,[status(thm)],[c_0_85])).
% 0.21/0.46  cnf(c_0_90, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk1_1(esk6_0),k3_subset_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_68, c_0_86])).
% 0.21/0.46  cnf(c_0_91, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_77])).
% 0.21/0.46  cnf(c_0_92, negated_conjecture, (~r2_hidden(esk1_1(esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91])).
% 0.21/0.46  cnf(c_0_93, negated_conjecture, (~r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0!=k1_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.46  cnf(c_0_94, negated_conjecture, (v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_92, c_0_82])).
% 0.21/0.46  cnf(c_0_95, negated_conjecture, (esk6_0!=k1_xboole_0|~r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(rw,[status(thm)],[c_0_93, c_0_52])).
% 0.21/0.46  cnf(c_0_96, negated_conjecture, (esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_83, c_0_94])).
% 0.21/0.46  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96]), c_0_96]), c_0_96]), c_0_59])]), ['proof']).
% 0.21/0.46  # SZS output end CNFRefutation
% 0.21/0.46  # Proof object total steps             : 98
% 0.21/0.46  # Proof object clause steps            : 63
% 0.21/0.46  # Proof object formula steps           : 35
% 0.21/0.46  # Proof object conjectures             : 18
% 0.21/0.46  # Proof object clause conjectures      : 15
% 0.21/0.46  # Proof object formula conjectures     : 3
% 0.21/0.46  # Proof object initial clauses used    : 23
% 0.21/0.46  # Proof object initial formulas used   : 17
% 0.21/0.46  # Proof object generating inferences   : 21
% 0.21/0.46  # Proof object simplifying inferences  : 48
% 0.21/0.46  # Training examples: 0 positive, 0 negative
% 0.21/0.46  # Parsed axioms                        : 23
% 0.21/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.46  # Initial clauses                      : 41
% 0.21/0.46  # Removed in clause preprocessing      : 3
% 0.21/0.46  # Initial clauses in saturation        : 38
% 0.21/0.46  # Processed clauses                    : 522
% 0.21/0.46  # ...of these trivial                  : 19
% 0.21/0.46  # ...subsumed                          : 241
% 0.21/0.46  # ...remaining for further processing  : 262
% 0.21/0.46  # Other redundant clauses eliminated   : 42
% 0.21/0.46  # Clauses deleted for lack of memory   : 0
% 0.21/0.46  # Backward-subsumed                    : 12
% 0.21/0.46  # Backward-rewritten                   : 110
% 0.21/0.46  # Generated clauses                    : 3424
% 0.21/0.46  # ...of the previous two non-trivial   : 3130
% 0.21/0.46  # Contextual simplify-reflections      : 6
% 0.21/0.46  # Paramodulations                      : 3319
% 0.21/0.46  # Factorizations                       : 18
% 0.21/0.46  # Equation resolutions                 : 87
% 0.21/0.46  # Propositional unsat checks           : 0
% 0.21/0.46  #    Propositional check models        : 0
% 0.21/0.46  #    Propositional check unsatisfiable : 0
% 0.21/0.46  #    Propositional clauses             : 0
% 0.21/0.46  #    Propositional clauses after purity: 0
% 0.21/0.46  #    Propositional unsat core size     : 0
% 0.21/0.46  #    Propositional preprocessing time  : 0.000
% 0.21/0.46  #    Propositional encoding time       : 0.000
% 0.21/0.46  #    Propositional solver time         : 0.000
% 0.21/0.46  #    Success case prop preproc time    : 0.000
% 0.21/0.46  #    Success case prop encoding time   : 0.000
% 0.21/0.46  #    Success case prop solver time     : 0.000
% 0.21/0.46  # Current number of processed clauses  : 138
% 0.21/0.46  #    Positive orientable unit clauses  : 30
% 0.21/0.46  #    Positive unorientable unit clauses: 8
% 0.21/0.46  #    Negative unit clauses             : 6
% 0.21/0.46  #    Non-unit-clauses                  : 94
% 0.21/0.46  # Current number of unprocessed clauses: 2372
% 0.21/0.46  # ...number of literals in the above   : 6220
% 0.21/0.46  # Current number of archived formulas  : 0
% 0.21/0.46  # Current number of archived clauses   : 125
% 0.21/0.46  # Clause-clause subsumption calls (NU) : 6434
% 0.21/0.46  # Rec. Clause-clause subsumption calls : 4874
% 0.21/0.46  # Non-unit clause-clause subsumptions  : 139
% 0.21/0.46  # Unit Clause-clause subsumption calls : 607
% 0.21/0.46  # Rewrite failures with RHS unbound    : 0
% 0.21/0.46  # BW rewrite match attempts            : 508
% 0.21/0.46  # BW rewrite match successes           : 192
% 0.21/0.46  # Condensation attempts                : 0
% 0.21/0.46  # Condensation successes               : 0
% 0.21/0.46  # Termbank termtop insertions          : 54162
% 0.21/0.46  
% 0.21/0.46  # -------------------------------------------------
% 0.21/0.46  # User time                : 0.116 s
% 0.21/0.46  # System time              : 0.010 s
% 0.21/0.46  # Total time               : 0.125 s
% 0.21/0.46  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
