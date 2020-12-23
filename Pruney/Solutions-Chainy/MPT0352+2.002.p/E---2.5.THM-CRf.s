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
% DateTime   : Thu Dec  3 10:45:36 EST 2020

% Result     : Theorem 8.72s
% Output     : CNFRefutation 8.72s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 307 expanded)
%              Number of clauses        :   70 ( 137 expanded)
%              Number of leaves         :   26 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  244 ( 608 expanded)
%              Number of equality atoms :   54 ( 185 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

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

fof(t34_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t73_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

fof(c_0_27,plain,(
    ! [X57,X58] :
      ( ( ~ m1_subset_1(X58,X57)
        | r2_hidden(X58,X57)
        | v1_xboole_0(X57) )
      & ( ~ r2_hidden(X58,X57)
        | m1_subset_1(X58,X57)
        | v1_xboole_0(X57) )
      & ( ~ m1_subset_1(X58,X57)
        | v1_xboole_0(X58)
        | ~ v1_xboole_0(X57) )
      & ( ~ v1_xboole_0(X58)
        | m1_subset_1(X58,X57)
        | ~ v1_xboole_0(X57) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_28,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))
    & ( ~ r1_tarski(esk5_0,esk6_0)
      | ~ r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) )
    & ( r1_tarski(esk5_0,esk6_0)
      | r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_29,plain,(
    ! [X61] : ~ v1_xboole_0(k1_zfmisc_1(X61)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_30,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(X24,X25)
      | r1_tarski(k4_xboole_0(X26,X25),k4_xboole_0(X26,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).

fof(c_0_31,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_32,plain,(
    ! [X59,X60] :
      ( ~ m1_subset_1(X60,k1_zfmisc_1(X59))
      | k3_subset_1(X59,X60) = k4_xboole_0(X59,X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_33,plain,(
    ! [X48,X49,X50,X51,X52,X53] :
      ( ( ~ r2_hidden(X50,X49)
        | r1_tarski(X50,X48)
        | X49 != k1_zfmisc_1(X48) )
      & ( ~ r1_tarski(X51,X48)
        | r2_hidden(X51,X49)
        | X49 != k1_zfmisc_1(X48) )
      & ( ~ r2_hidden(esk3_2(X52,X53),X53)
        | ~ r1_tarski(esk3_2(X52,X53),X52)
        | X53 = k1_zfmisc_1(X52) )
      & ( r2_hidden(esk3_2(X52,X53),X53)
        | r1_tarski(esk3_2(X52,X53),X52)
        | X53 = k1_zfmisc_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_37,plain,(
    ! [X27,X28] : r1_tarski(k4_xboole_0(X27,X28),X27) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_38,plain,
    ( r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

fof(c_0_43,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,X22)
      | ~ r1_tarski(X22,X23)
      | r1_tarski(X21,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_44,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_45,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_46,plain,
    ( r1_tarski(k5_xboole_0(X3,k3_xboole_0(X3,X2)),k5_xboole_0(X3,k3_xboole_0(X3,X1)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_39])).

cnf(c_0_47,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_39])).

fof(c_0_48,plain,(
    ! [X38,X39] : r1_xboole_0(k4_xboole_0(X38,X39),X39) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | k1_zfmisc_1(esk4_0) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_50,plain,(
    ! [X55,X56] : k3_tarski(k2_tarski(X55,X56)) = k2_xboole_0(X55,X56) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_51,plain,(
    ! [X46,X47] : k1_enumset1(X46,X46,X47) = k2_tarski(X46,X47) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_52,plain,(
    ! [X18,X19,X20] :
      ( ( r1_tarski(X18,X19)
        | ~ r1_tarski(X18,k4_xboole_0(X19,X20)) )
      & ( r1_xboole_0(X18,X20)
        | ~ r1_tarski(X18,k4_xboole_0(X19,X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0)
    | r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_55,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_44,c_0_39])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_subset_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_58,plain,(
    ! [X33,X34] :
      ( v1_xboole_0(X34)
      | ~ r1_tarski(X34,X33)
      | ~ r1_xboole_0(X34,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_59,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk6_0,esk4_0) ),
    inference(er,[status(thm)],[c_0_49])).

fof(c_0_61,plain,(
    ! [X35,X36,X37] :
      ( ~ r1_tarski(X35,k2_xboole_0(X36,X37))
      | ~ r1_xboole_0(X35,X37)
      | r1_tarski(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).

cnf(c_0_62,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_64,plain,(
    ! [X29,X30] : k2_xboole_0(X29,k4_xboole_0(X30,X29)) = k2_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk4_0,esk5_0))
    | r1_tarski(esk5_0,esk6_0)
    | ~ r1_tarski(X1,k3_subset_1(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_67,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(esk5_0,esk6_0)
    | ~ r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_69,plain,
    ( r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_47])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_71,plain,(
    ! [X42,X43] : k2_xboole_0(X42,X43) = k5_xboole_0(X42,k4_xboole_0(X43,X42)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_72,plain,(
    ! [X40,X41] :
      ( ~ v1_xboole_0(X40)
      | X40 = X41
      | ~ v1_xboole_0(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_73,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_74,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_59,c_0_39])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_60])).

fof(c_0_76,plain,(
    ! [X31] : k4_xboole_0(X31,k1_xboole_0) = X31 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_77,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r1_xboole_0(X8,X9)
        | r2_hidden(esk1_2(X8,X9),k3_xboole_0(X8,X9)) )
      & ( ~ r2_hidden(X13,k3_xboole_0(X11,X12))
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_78,plain,(
    ! [X14] :
      ( X14 = k1_xboole_0
      | r2_hidden(esk2_1(X14),X14) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_80,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_81,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_82,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_65,c_0_39])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k3_subset_1(esk4_0,esk6_0),k3_xboole_0(X1,k3_subset_1(esk4_0,esk6_0))),k3_subset_1(esk4_0,esk5_0))
    | r1_tarski(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_84,negated_conjecture,
    ( ~ r1_tarski(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_35])])).

cnf(c_0_85,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_86,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_87,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_88,plain,
    ( v1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X1)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_55])).

cnf(c_0_90,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_91,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_92,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

fof(c_0_93,plain,(
    ! [X32] : r1_xboole_0(X32,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_95,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_tarski(k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_80]),c_0_80]),c_0_39])).

fof(c_0_96,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_97,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k3_subset_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_47])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k3_subset_1(esk4_0,esk6_0),k3_xboole_0(X1,k3_subset_1(esk4_0,esk6_0))),k3_subset_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[c_0_83,c_0_84])).

fof(c_0_99,plain,(
    ! [X44,X45] : k2_tarski(X44,X45) = k2_tarski(X45,X44) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_100,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_80]),c_0_39])).

cnf(c_0_101,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_102,negated_conjecture,
    ( v1_xboole_0(k5_xboole_0(esk6_0,k3_xboole_0(esk4_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_56])).

cnf(c_0_103,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_90,c_0_39])).

cnf(c_0_104,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_105,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_70]),c_0_36])).

cnf(c_0_107,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_108,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k3_subset_1(X2,X1))) = k3_tarski(k1_enumset1(X1,X1,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_47])).

cnf(c_0_109,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_110,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(k3_subset_1(esk4_0,esk6_0),k3_xboole_0(X1,k3_subset_1(esk4_0,esk6_0))),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_70])])).

cnf(c_0_111,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_112,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k3_tarski(k1_enumset1(X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_56])).

cnf(c_0_113,negated_conjecture,
    ( k5_xboole_0(esk6_0,k3_xboole_0(esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_114,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_105])])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | k1_zfmisc_1(esk4_0) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_106])).

cnf(c_0_116,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r1_xboole_0(X1,k5_xboole_0(k3_subset_1(X3,X2),k3_xboole_0(X2,k3_subset_1(X3,X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_56])).

cnf(c_0_117,negated_conjecture,
    ( r1_xboole_0(esk5_0,k5_xboole_0(k3_subset_1(esk4_0,esk6_0),k3_xboole_0(X1,k3_subset_1(esk4_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_118,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_63]),c_0_63])).

cnf(c_0_119,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk4_0,esk4_0,esk6_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(er,[status(thm)],[c_0_115])).

cnf(c_0_121,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_35]),c_0_118]),c_0_119]),c_0_120])]),c_0_84]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:33:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 8.72/8.92  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 8.72/8.92  # and selection function PSelectComplexExceptUniqMaxHorn.
% 8.72/8.92  #
% 8.72/8.92  # Preprocessing time       : 0.029 s
% 8.72/8.92  
% 8.72/8.92  # Proof found!
% 8.72/8.92  # SZS status Theorem
% 8.72/8.92  # SZS output start CNFRefutation
% 8.72/8.92  fof(t31_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 8.72/8.92  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 8.72/8.92  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 8.72/8.92  fof(t34_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 8.72/8.92  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.72/8.92  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 8.72/8.92  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 8.72/8.92  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.72/8.92  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.72/8.92  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.72/8.92  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 8.72/8.92  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.72/8.92  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 8.72/8.92  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 8.72/8.92  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 8.72/8.92  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 8.72/8.92  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.72/8.92  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.72/8.92  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 8.72/8.92  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.72/8.92  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.72/8.92  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.72/8.92  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.72/8.92  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.72/8.92  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.72/8.92  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.72/8.92  fof(c_0_26, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_subset_1])).
% 8.72/8.92  fof(c_0_27, plain, ![X57, X58]:(((~m1_subset_1(X58,X57)|r2_hidden(X58,X57)|v1_xboole_0(X57))&(~r2_hidden(X58,X57)|m1_subset_1(X58,X57)|v1_xboole_0(X57)))&((~m1_subset_1(X58,X57)|v1_xboole_0(X58)|~v1_xboole_0(X57))&(~v1_xboole_0(X58)|m1_subset_1(X58,X57)|~v1_xboole_0(X57)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 8.72/8.92  fof(c_0_28, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))&((~r1_tarski(esk5_0,esk6_0)|~r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)))&(r1_tarski(esk5_0,esk6_0)|r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 8.72/8.92  fof(c_0_29, plain, ![X61]:~v1_xboole_0(k1_zfmisc_1(X61)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 8.72/8.92  fof(c_0_30, plain, ![X24, X25, X26]:(~r1_tarski(X24,X25)|r1_tarski(k4_xboole_0(X26,X25),k4_xboole_0(X26,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).
% 8.72/8.92  fof(c_0_31, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 8.72/8.92  fof(c_0_32, plain, ![X59, X60]:(~m1_subset_1(X60,k1_zfmisc_1(X59))|k3_subset_1(X59,X60)=k4_xboole_0(X59,X60)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 8.72/8.92  fof(c_0_33, plain, ![X48, X49, X50, X51, X52, X53]:(((~r2_hidden(X50,X49)|r1_tarski(X50,X48)|X49!=k1_zfmisc_1(X48))&(~r1_tarski(X51,X48)|r2_hidden(X51,X49)|X49!=k1_zfmisc_1(X48)))&((~r2_hidden(esk3_2(X52,X53),X53)|~r1_tarski(esk3_2(X52,X53),X52)|X53=k1_zfmisc_1(X52))&(r2_hidden(esk3_2(X52,X53),X53)|r1_tarski(esk3_2(X52,X53),X52)|X53=k1_zfmisc_1(X52)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 8.72/8.92  cnf(c_0_34, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 8.72/8.92  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 8.72/8.92  cnf(c_0_36, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 8.72/8.92  fof(c_0_37, plain, ![X27, X28]:r1_tarski(k4_xboole_0(X27,X28),X27), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 8.72/8.92  cnf(c_0_38, plain, (r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 8.72/8.92  cnf(c_0_39, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 8.72/8.92  cnf(c_0_40, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 8.72/8.92  cnf(c_0_41, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 8.72/8.92  cnf(c_0_42, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 8.72/8.92  fof(c_0_43, plain, ![X21, X22, X23]:(~r1_tarski(X21,X22)|~r1_tarski(X22,X23)|r1_tarski(X21,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 8.72/8.92  cnf(c_0_44, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 8.72/8.92  fof(c_0_45, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 8.72/8.92  cnf(c_0_46, plain, (r1_tarski(k5_xboole_0(X3,k3_xboole_0(X3,X2)),k5_xboole_0(X3,k3_xboole_0(X3,X1)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_39])).
% 8.72/8.92  cnf(c_0_47, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_40, c_0_39])).
% 8.72/8.92  fof(c_0_48, plain, ![X38, X39]:r1_xboole_0(k4_xboole_0(X38,X39),X39), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 8.72/8.92  cnf(c_0_49, negated_conjecture, (r1_tarski(esk6_0,X1)|k1_zfmisc_1(esk4_0)!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 8.72/8.92  fof(c_0_50, plain, ![X55, X56]:k3_tarski(k2_tarski(X55,X56))=k2_xboole_0(X55,X56), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 8.72/8.92  fof(c_0_51, plain, ![X46, X47]:k1_enumset1(X46,X46,X47)=k2_tarski(X46,X47), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 8.72/8.92  fof(c_0_52, plain, ![X18, X19, X20]:((r1_tarski(X18,X19)|~r1_tarski(X18,k4_xboole_0(X19,X20)))&(r1_xboole_0(X18,X20)|~r1_tarski(X18,k4_xboole_0(X19,X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 8.72/8.92  cnf(c_0_53, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 8.72/8.92  cnf(c_0_54, negated_conjecture, (r1_tarski(esk5_0,esk6_0)|r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 8.72/8.92  cnf(c_0_55, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_44, c_0_39])).
% 8.72/8.92  cnf(c_0_56, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 8.72/8.92  cnf(c_0_57, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_subset_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 8.72/8.92  fof(c_0_58, plain, ![X33, X34]:(v1_xboole_0(X34)|(~r1_tarski(X34,X33)|~r1_xboole_0(X34,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 8.72/8.92  cnf(c_0_59, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 8.72/8.92  cnf(c_0_60, negated_conjecture, (r1_tarski(esk6_0,esk4_0)), inference(er,[status(thm)],[c_0_49])).
% 8.72/8.92  fof(c_0_61, plain, ![X35, X36, X37]:(~r1_tarski(X35,k2_xboole_0(X36,X37))|~r1_xboole_0(X35,X37)|r1_tarski(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 8.72/8.92  cnf(c_0_62, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 8.72/8.92  cnf(c_0_63, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 8.72/8.92  fof(c_0_64, plain, ![X29, X30]:k2_xboole_0(X29,k4_xboole_0(X30,X29))=k2_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 8.72/8.92  cnf(c_0_65, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 8.72/8.92  cnf(c_0_66, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk4_0,esk5_0))|r1_tarski(esk5_0,esk6_0)|~r1_tarski(X1,k3_subset_1(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 8.72/8.92  cnf(c_0_67, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 8.72/8.92  cnf(c_0_68, negated_conjecture, (~r1_tarski(esk5_0,esk6_0)|~r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 8.72/8.92  cnf(c_0_69, plain, (r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_57, c_0_47])).
% 8.72/8.92  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 8.72/8.92  fof(c_0_71, plain, ![X42, X43]:k2_xboole_0(X42,X43)=k5_xboole_0(X42,k4_xboole_0(X43,X42)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 8.72/8.92  fof(c_0_72, plain, ![X40, X41]:(~v1_xboole_0(X40)|X40=X41|~v1_xboole_0(X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 8.72/8.92  cnf(c_0_73, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 8.72/8.92  cnf(c_0_74, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_59, c_0_39])).
% 8.72/8.92  cnf(c_0_75, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_53, c_0_60])).
% 8.72/8.92  fof(c_0_76, plain, ![X31]:k4_xboole_0(X31,k1_xboole_0)=X31, inference(variable_rename,[status(thm)],[t3_boole])).
% 8.72/8.92  fof(c_0_77, plain, ![X8, X9, X11, X12, X13]:((r1_xboole_0(X8,X9)|r2_hidden(esk1_2(X8,X9),k3_xboole_0(X8,X9)))&(~r2_hidden(X13,k3_xboole_0(X11,X12))|~r1_xboole_0(X11,X12))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 8.72/8.92  fof(c_0_78, plain, ![X14]:(X14=k1_xboole_0|r2_hidden(esk2_1(X14),X14)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 8.72/8.92  cnf(c_0_79, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 8.72/8.92  cnf(c_0_80, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 8.72/8.92  cnf(c_0_81, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 8.72/8.92  cnf(c_0_82, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_65, c_0_39])).
% 8.72/8.92  cnf(c_0_83, negated_conjecture, (r1_tarski(k5_xboole_0(k3_subset_1(esk4_0,esk6_0),k3_xboole_0(X1,k3_subset_1(esk4_0,esk6_0))),k3_subset_1(esk4_0,esk5_0))|r1_tarski(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 8.72/8.92  cnf(c_0_84, negated_conjecture, (~r1_tarski(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_35])])).
% 8.72/8.92  cnf(c_0_85, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 8.72/8.92  cnf(c_0_86, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 8.72/8.92  cnf(c_0_87, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 8.72/8.92  cnf(c_0_88, plain, (v1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)))|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 8.72/8.92  cnf(c_0_89, negated_conjecture, (r1_tarski(k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X1)),esk4_0)), inference(spm,[status(thm)],[c_0_75, c_0_55])).
% 8.72/8.92  cnf(c_0_90, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_76])).
% 8.72/8.92  cnf(c_0_91, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 8.72/8.92  cnf(c_0_92, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 8.72/8.92  fof(c_0_93, plain, ![X32]:r1_xboole_0(X32,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 8.72/8.92  cnf(c_0_94, plain, (r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)|~r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_79, c_0_80])).
% 8.72/8.92  cnf(c_0_95, plain, (k3_tarski(k1_enumset1(X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k3_tarski(k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_80]), c_0_80]), c_0_39])).
% 8.72/8.92  fof(c_0_96, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 8.72/8.92  cnf(c_0_97, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k3_subset_1(X3,X2))), inference(spm,[status(thm)],[c_0_82, c_0_47])).
% 8.72/8.92  cnf(c_0_98, negated_conjecture, (r1_tarski(k5_xboole_0(k3_subset_1(esk4_0,esk6_0),k3_xboole_0(X1,k3_subset_1(esk4_0,esk6_0))),k3_subset_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[c_0_83, c_0_84])).
% 8.72/8.92  fof(c_0_99, plain, ![X44, X45]:k2_tarski(X44,X45)=k2_tarski(X45,X44), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 8.72/8.92  cnf(c_0_100, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_80]), c_0_39])).
% 8.72/8.92  cnf(c_0_101, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 8.72/8.92  cnf(c_0_102, negated_conjecture, (v1_xboole_0(k5_xboole_0(esk6_0,k3_xboole_0(esk4_0,esk6_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_56])).
% 8.72/8.92  cnf(c_0_103, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_90, c_0_39])).
% 8.72/8.92  cnf(c_0_104, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 8.72/8.92  cnf(c_0_105, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 8.72/8.92  cnf(c_0_106, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_70]), c_0_36])).
% 8.72/8.92  cnf(c_0_107, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 8.72/8.92  cnf(c_0_108, plain, (k3_tarski(k1_enumset1(X1,X1,k3_subset_1(X2,X1)))=k3_tarski(k1_enumset1(X1,X1,X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_95, c_0_47])).
% 8.72/8.92  cnf(c_0_109, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 8.72/8.92  cnf(c_0_110, negated_conjecture, (r1_xboole_0(k5_xboole_0(k3_subset_1(esk4_0,esk6_0),k3_xboole_0(X1,k3_subset_1(esk4_0,esk6_0))),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_70])])).
% 8.72/8.92  cnf(c_0_111, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 8.72/8.92  cnf(c_0_112, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k3_tarski(k1_enumset1(X1,X1,X2))), inference(spm,[status(thm)],[c_0_100, c_0_56])).
% 8.72/8.92  cnf(c_0_113, negated_conjecture, (k5_xboole_0(esk6_0,k3_xboole_0(esk4_0,esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 8.72/8.92  cnf(c_0_114, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_105])])).
% 8.72/8.92  cnf(c_0_115, negated_conjecture, (r1_tarski(esk5_0,X1)|k1_zfmisc_1(esk4_0)!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_106])).
% 8.72/8.92  cnf(c_0_116, plain, (r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r1_xboole_0(X1,k5_xboole_0(k3_subset_1(X3,X2),k3_xboole_0(X2,k3_subset_1(X3,X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_56])).
% 8.72/8.92  cnf(c_0_117, negated_conjecture, (r1_xboole_0(esk5_0,k5_xboole_0(k3_subset_1(esk4_0,esk6_0),k3_xboole_0(X1,k3_subset_1(esk4_0,esk6_0))))), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 8.72/8.92  cnf(c_0_118, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_63]), c_0_63])).
% 8.72/8.92  cnf(c_0_119, negated_conjecture, (k3_tarski(k1_enumset1(esk4_0,esk4_0,esk6_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_114])).
% 8.72/8.92  cnf(c_0_120, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(er,[status(thm)],[c_0_115])).
% 8.72/8.92  cnf(c_0_121, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_35]), c_0_118]), c_0_119]), c_0_120])]), c_0_84]), ['proof']).
% 8.72/8.92  # SZS output end CNFRefutation
% 8.72/8.92  # Proof object total steps             : 122
% 8.72/8.92  # Proof object clause steps            : 70
% 8.72/8.92  # Proof object formula steps           : 52
% 8.72/8.92  # Proof object conjectures             : 25
% 8.72/8.92  # Proof object clause conjectures      : 22
% 8.72/8.92  # Proof object formula conjectures     : 3
% 8.72/8.92  # Proof object initial clauses used    : 29
% 8.72/8.92  # Proof object initial formulas used   : 26
% 8.72/8.92  # Proof object generating inferences   : 29
% 8.72/8.92  # Proof object simplifying inferences  : 35
% 8.72/8.92  # Training examples: 0 positive, 0 negative
% 8.72/8.92  # Parsed axioms                        : 26
% 8.72/8.92  # Removed by relevancy pruning/SinE    : 0
% 8.72/8.92  # Initial clauses                      : 37
% 8.72/8.92  # Removed in clause preprocessing      : 3
% 8.72/8.92  # Initial clauses in saturation        : 34
% 8.72/8.92  # Processed clauses                    : 47093
% 8.72/8.92  # ...of these trivial                  : 754
% 8.72/8.92  # ...subsumed                          : 40573
% 8.72/8.92  # ...remaining for further processing  : 5766
% 8.72/8.92  # Other redundant clauses eliminated   : 0
% 8.72/8.92  # Clauses deleted for lack of memory   : 0
% 8.72/8.92  # Backward-subsumed                    : 457
% 8.72/8.92  # Backward-rewritten                   : 208
% 8.72/8.92  # Generated clauses                    : 787928
% 8.72/8.92  # ...of the previous two non-trivial   : 667848
% 8.72/8.92  # Contextual simplify-reflections      : 64
% 8.72/8.92  # Paramodulations                      : 787473
% 8.72/8.92  # Factorizations                       : 88
% 8.72/8.92  # Equation resolutions                 : 348
% 8.72/8.92  # Propositional unsat checks           : 0
% 8.72/8.92  #    Propositional check models        : 0
% 8.72/8.92  #    Propositional check unsatisfiable : 0
% 8.72/8.92  #    Propositional clauses             : 0
% 8.72/8.92  #    Propositional clauses after purity: 0
% 8.72/8.92  #    Propositional unsat core size     : 0
% 8.72/8.92  #    Propositional preprocessing time  : 0.000
% 8.72/8.92  #    Propositional encoding time       : 0.000
% 8.72/8.92  #    Propositional solver time         : 0.000
% 8.72/8.92  #    Success case prop preproc time    : 0.000
% 8.72/8.92  #    Success case prop encoding time   : 0.000
% 8.72/8.92  #    Success case prop solver time     : 0.000
% 8.72/8.92  # Current number of processed clauses  : 5082
% 8.72/8.92  #    Positive orientable unit clauses  : 314
% 8.72/8.92  #    Positive unorientable unit clauses: 2
% 8.72/8.92  #    Negative unit clauses             : 107
% 8.72/8.92  #    Non-unit-clauses                  : 4659
% 8.72/8.92  # Current number of unprocessed clauses: 616420
% 8.72/8.92  # ...number of literals in the above   : 2190381
% 8.72/8.92  # Current number of archived formulas  : 0
% 8.72/8.92  # Current number of archived clauses   : 687
% 8.72/8.92  # Clause-clause subsumption calls (NU) : 2363441
% 8.72/8.92  # Rec. Clause-clause subsumption calls : 1722544
% 8.72/8.92  # Non-unit clause-clause subsumptions  : 19778
% 8.72/8.92  # Unit Clause-clause subsumption calls : 39579
% 8.72/8.92  # Rewrite failures with RHS unbound    : 74
% 8.72/8.92  # BW rewrite match attempts            : 2664
% 8.72/8.92  # BW rewrite match successes           : 161
% 8.72/8.92  # Condensation attempts                : 0
% 8.72/8.92  # Condensation successes               : 0
% 8.72/8.92  # Termbank termtop insertions          : 16333718
% 8.74/8.95  
% 8.74/8.95  # -------------------------------------------------
% 8.74/8.95  # User time                : 8.234 s
% 8.74/8.95  # System time              : 0.343 s
% 8.74/8.95  # Total time               : 8.577 s
% 8.74/8.95  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
