%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:40 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 373 expanded)
%              Number of clauses        :   51 ( 153 expanded)
%              Number of leaves         :   22 ( 108 expanded)
%              Depth                    :   12
%              Number of atoms          :  238 ( 633 expanded)
%              Number of equality atoms :   81 ( 372 expanded)
%              Maximal formula depth    :   32 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(d3_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( X6 = k3_enumset1(X1,X2,X3,X4,X5)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X7 != X1
              & X7 != X2
              & X7 != X3
              & X7 != X4
              & X7 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t48_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( r1_tarski(X1,X2)
               => r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t7_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ( X1 = k1_xboole_0
        | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(c_0_22,plain,(
    ! [X59,X60] : k1_setfam_1(k2_tarski(X59,X60)) = k3_xboole_0(X59,X60) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_23,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X20,X21] : r1_xboole_0(k4_xboole_0(X20,X21),X21) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_30,plain,(
    ! [X26,X27,X28] : k2_enumset1(X26,X26,X27,X28) = k1_enumset1(X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_31,plain,(
    ! [X29,X30,X31,X32] : k3_enumset1(X29,X29,X30,X31,X32) = k2_enumset1(X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_32,plain,(
    ! [X33,X34,X35,X36,X37] : k4_enumset1(X33,X33,X34,X35,X36,X37) = k3_enumset1(X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_33,plain,(
    ! [X8] : k3_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_34,plain,(
    ! [X16,X17] : r1_tarski(k4_xboole_0(X16,X17),X16) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_35,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

fof(c_0_43,plain,(
    ! [X22,X23] :
      ( ~ v1_xboole_0(X22)
      | X22 = X23
      | ~ v1_xboole_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_44,plain,(
    ! [X18,X19] :
      ( v1_xboole_0(X19)
      | ~ r1_tarski(X19,X18)
      | ~ r1_xboole_0(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_45,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_46,plain,
    ( k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_29]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_47,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_36]),c_0_37]),c_0_38]),c_0_39])).

fof(c_0_48,plain,(
    ! [X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57] :
      ( ( ~ r2_hidden(X50,X49)
        | X50 = X44
        | X50 = X45
        | X50 = X46
        | X50 = X47
        | X50 = X48
        | X49 != k3_enumset1(X44,X45,X46,X47,X48) )
      & ( X51 != X44
        | r2_hidden(X51,X49)
        | X49 != k3_enumset1(X44,X45,X46,X47,X48) )
      & ( X51 != X45
        | r2_hidden(X51,X49)
        | X49 != k3_enumset1(X44,X45,X46,X47,X48) )
      & ( X51 != X46
        | r2_hidden(X51,X49)
        | X49 != k3_enumset1(X44,X45,X46,X47,X48) )
      & ( X51 != X47
        | r2_hidden(X51,X49)
        | X49 != k3_enumset1(X44,X45,X46,X47,X48) )
      & ( X51 != X48
        | r2_hidden(X51,X49)
        | X49 != k3_enumset1(X44,X45,X46,X47,X48) )
      & ( esk1_6(X52,X53,X54,X55,X56,X57) != X52
        | ~ r2_hidden(esk1_6(X52,X53,X54,X55,X56,X57),X57)
        | X57 = k3_enumset1(X52,X53,X54,X55,X56) )
      & ( esk1_6(X52,X53,X54,X55,X56,X57) != X53
        | ~ r2_hidden(esk1_6(X52,X53,X54,X55,X56,X57),X57)
        | X57 = k3_enumset1(X52,X53,X54,X55,X56) )
      & ( esk1_6(X52,X53,X54,X55,X56,X57) != X54
        | ~ r2_hidden(esk1_6(X52,X53,X54,X55,X56,X57),X57)
        | X57 = k3_enumset1(X52,X53,X54,X55,X56) )
      & ( esk1_6(X52,X53,X54,X55,X56,X57) != X55
        | ~ r2_hidden(esk1_6(X52,X53,X54,X55,X56,X57),X57)
        | X57 = k3_enumset1(X52,X53,X54,X55,X56) )
      & ( esk1_6(X52,X53,X54,X55,X56,X57) != X56
        | ~ r2_hidden(esk1_6(X52,X53,X54,X55,X56,X57),X57)
        | X57 = k3_enumset1(X52,X53,X54,X55,X56) )
      & ( r2_hidden(esk1_6(X52,X53,X54,X55,X56,X57),X57)
        | esk1_6(X52,X53,X54,X55,X56,X57) = X52
        | esk1_6(X52,X53,X54,X55,X56,X57) = X53
        | esk1_6(X52,X53,X54,X55,X56,X57) = X54
        | esk1_6(X52,X53,X54,X55,X56,X57) = X55
        | esk1_6(X52,X53,X54,X55,X56,X57) = X56
        | X57 = k3_enumset1(X52,X53,X54,X55,X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).

fof(c_0_49,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & ~ r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).

fof(c_0_50,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X13,X15)
      | r1_tarski(X13,k3_xboole_0(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_51,plain,(
    ! [X65,X66] :
      ( ~ v1_relat_1(X65)
      | ~ m1_subset_1(X66,k1_zfmisc_1(X65))
      | v1_relat_1(X66) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_52,plain,(
    ! [X61,X62] :
      ( ( ~ m1_subset_1(X61,k1_zfmisc_1(X62))
        | r1_tarski(X61,X62) )
      & ( ~ r1_tarski(X61,X62)
        | m1_subset_1(X61,k1_zfmisc_1(X62)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_53,plain,(
    ! [X41,X42,X43] :
      ( ( ~ r2_hidden(X41,X43)
        | k4_xboole_0(k2_tarski(X41,X42),X43) != k2_tarski(X41,X42) )
      & ( ~ r2_hidden(X42,X43)
        | k4_xboole_0(k2_tarski(X41,X42),X43) != k2_tarski(X41,X42) )
      & ( r2_hidden(X41,X43)
        | r2_hidden(X42,X43)
        | k4_xboole_0(k2_tarski(X41,X42),X43) = k2_tarski(X41,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

cnf(c_0_54,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_56,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_57,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_58,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X5,X6,X7,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_62,plain,(
    ! [X67,X68,X69] :
      ( ~ v1_relat_1(X67)
      | ~ v1_relat_1(X68)
      | ~ v1_relat_1(X69)
      | ~ r1_tarski(X67,X68)
      | r1_tarski(k5_relat_1(X69,X67),k5_relat_1(X69,X68)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).

cnf(c_0_63,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k2_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_67,plain,
    ( v1_xboole_0(k5_xboole_0(X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X4,X5,X6,X7,X2) ),
    inference(rw,[status(thm)],[c_0_59,c_0_39])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k4_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_29]),c_0_29]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_29]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_71,plain,
    ( r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_73,plain,(
    ! [X11,X12] : r1_tarski(k3_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_74,plain,(
    ! [X63,X64] :
      ( ~ r1_tarski(X63,X64)
      | X63 = k1_xboole_0
      | r1_tarski(k1_setfam_1(X64),k1_setfam_1(X63)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_setfam_1])])).

cnf(c_0_75,plain,
    ( k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X1),k1_setfam_1(k4_enumset1(k4_enumset1(X3,X3,X3,X3,X3,X1),k4_enumset1(X3,X3,X3,X3,X3,X1),k4_enumset1(X3,X3,X3,X3,X3,X1),k4_enumset1(X3,X3,X3,X3,X3,X1),k4_enumset1(X3,X3,X3,X3,X3,X1),X2))) != k4_enumset1(X3,X3,X3,X3,X3,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_26]),c_0_26]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,k4_enumset1(X2,X2,X3,X4,X5,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_68])])).

fof(c_0_78,plain,(
    ! [X38,X39,X40] :
      ( ( r2_hidden(X38,X40)
        | ~ r1_tarski(k2_tarski(X38,X39),X40) )
      & ( r2_hidden(X39,X40)
        | ~ r1_tarski(k2_tarski(X38,X39),X40) )
      & ( ~ r2_hidden(X38,X40)
        | ~ r2_hidden(X39,X40)
        | r1_tarski(k2_tarski(X38,X39),X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k5_relat_1(esk2_0,esk4_0))
    | ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k5_relat_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_80,plain,
    ( r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X2,X3) ),
    inference(csr,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_82,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_83,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_84,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_85,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X2) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_46]),c_0_76]),c_0_77])])).

cnf(c_0_86,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k5_relat_1(esk2_0,esk3_0))
    | ~ r1_tarski(k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_82])])).

cnf(c_0_88,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_89,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_29]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_90,plain,
    ( r1_tarski(k1_setfam_1(X1),X2)
    | ~ r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X2),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_46]),c_0_85])).

cnf(c_0_91,plain,
    ( r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_26]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_92,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_80]),c_0_81]),c_0_88]),c_0_89])])).

cnf(c_0_93,plain,
    ( r1_tarski(k1_setfam_1(X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_77])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:14:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.14/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.029 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.14/0.38  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.14/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.14/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.14/0.38  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.14/0.38  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.14/0.38  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 0.14/0.38  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.14/0.38  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.14/0.38  fof(d3_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:(X6=k3_enumset1(X1,X2,X3,X4,X5)<=>![X7]:(r2_hidden(X7,X6)<=>~(((((X7!=X1&X7!=X2)&X7!=X3)&X7!=X4)&X7!=X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 0.14/0.38  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.14/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.14/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.14/0.38  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 0.14/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.14/0.38  fof(t48_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 0.14/0.38  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.14/0.38  fof(t7_setfam_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>(X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 0.14/0.38  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.14/0.38  fof(c_0_22, plain, ![X59, X60]:k1_setfam_1(k2_tarski(X59,X60))=k3_xboole_0(X59,X60), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.38  fof(c_0_23, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.38  fof(c_0_24, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.14/0.38  cnf(c_0_25, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.38  fof(c_0_27, plain, ![X20, X21]:r1_xboole_0(k4_xboole_0(X20,X21),X21), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.14/0.38  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_29, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.38  fof(c_0_30, plain, ![X26, X27, X28]:k2_enumset1(X26,X26,X27,X28)=k1_enumset1(X26,X27,X28), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.38  fof(c_0_31, plain, ![X29, X30, X31, X32]:k3_enumset1(X29,X29,X30,X31,X32)=k2_enumset1(X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.14/0.38  fof(c_0_32, plain, ![X33, X34, X35, X36, X37]:k4_enumset1(X33,X33,X34,X35,X36,X37)=k3_enumset1(X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.14/0.38  fof(c_0_33, plain, ![X8]:k3_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.14/0.38  fof(c_0_34, plain, ![X16, X17]:r1_tarski(k4_xboole_0(X16,X17),X16), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.14/0.38  cnf(c_0_35, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.38  cnf(c_0_36, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.38  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.38  cnf(c_0_39, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.38  cnf(c_0_40, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  cnf(c_0_41, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.38  fof(c_0_42, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 0.14/0.38  fof(c_0_43, plain, ![X22, X23]:(~v1_xboole_0(X22)|X22=X23|~v1_xboole_0(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.14/0.38  fof(c_0_44, plain, ![X18, X19]:(v1_xboole_0(X19)|(~r1_tarski(X19,X18)|~r1_xboole_0(X19,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.14/0.38  cnf(c_0_45, plain, (r1_xboole_0(k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.14/0.38  cnf(c_0_46, plain, (k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_29]), c_0_37]), c_0_38]), c_0_39])).
% 0.14/0.38  cnf(c_0_47, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.14/0.38  fof(c_0_48, plain, ![X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57]:(((~r2_hidden(X50,X49)|(X50=X44|X50=X45|X50=X46|X50=X47|X50=X48)|X49!=k3_enumset1(X44,X45,X46,X47,X48))&(((((X51!=X44|r2_hidden(X51,X49)|X49!=k3_enumset1(X44,X45,X46,X47,X48))&(X51!=X45|r2_hidden(X51,X49)|X49!=k3_enumset1(X44,X45,X46,X47,X48)))&(X51!=X46|r2_hidden(X51,X49)|X49!=k3_enumset1(X44,X45,X46,X47,X48)))&(X51!=X47|r2_hidden(X51,X49)|X49!=k3_enumset1(X44,X45,X46,X47,X48)))&(X51!=X48|r2_hidden(X51,X49)|X49!=k3_enumset1(X44,X45,X46,X47,X48))))&((((((esk1_6(X52,X53,X54,X55,X56,X57)!=X52|~r2_hidden(esk1_6(X52,X53,X54,X55,X56,X57),X57)|X57=k3_enumset1(X52,X53,X54,X55,X56))&(esk1_6(X52,X53,X54,X55,X56,X57)!=X53|~r2_hidden(esk1_6(X52,X53,X54,X55,X56,X57),X57)|X57=k3_enumset1(X52,X53,X54,X55,X56)))&(esk1_6(X52,X53,X54,X55,X56,X57)!=X54|~r2_hidden(esk1_6(X52,X53,X54,X55,X56,X57),X57)|X57=k3_enumset1(X52,X53,X54,X55,X56)))&(esk1_6(X52,X53,X54,X55,X56,X57)!=X55|~r2_hidden(esk1_6(X52,X53,X54,X55,X56,X57),X57)|X57=k3_enumset1(X52,X53,X54,X55,X56)))&(esk1_6(X52,X53,X54,X55,X56,X57)!=X56|~r2_hidden(esk1_6(X52,X53,X54,X55,X56,X57),X57)|X57=k3_enumset1(X52,X53,X54,X55,X56)))&(r2_hidden(esk1_6(X52,X53,X54,X55,X56,X57),X57)|(esk1_6(X52,X53,X54,X55,X56,X57)=X52|esk1_6(X52,X53,X54,X55,X56,X57)=X53|esk1_6(X52,X53,X54,X55,X56,X57)=X54|esk1_6(X52,X53,X54,X55,X56,X57)=X55|esk1_6(X52,X53,X54,X55,X56,X57)=X56)|X57=k3_enumset1(X52,X53,X54,X55,X56)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).
% 0.14/0.38  fof(c_0_49, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&~r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).
% 0.14/0.38  fof(c_0_50, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X13,X15)|r1_tarski(X13,k3_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.14/0.38  fof(c_0_51, plain, ![X65, X66]:(~v1_relat_1(X65)|(~m1_subset_1(X66,k1_zfmisc_1(X65))|v1_relat_1(X66))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.14/0.38  fof(c_0_52, plain, ![X61, X62]:((~m1_subset_1(X61,k1_zfmisc_1(X62))|r1_tarski(X61,X62))&(~r1_tarski(X61,X62)|m1_subset_1(X61,k1_zfmisc_1(X62)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.14/0.38  fof(c_0_53, plain, ![X41, X42, X43]:(((~r2_hidden(X41,X43)|k4_xboole_0(k2_tarski(X41,X42),X43)!=k2_tarski(X41,X42))&(~r2_hidden(X42,X43)|k4_xboole_0(k2_tarski(X41,X42),X43)!=k2_tarski(X41,X42)))&(r2_hidden(X41,X43)|r2_hidden(X42,X43)|k4_xboole_0(k2_tarski(X41,X42),X43)=k2_tarski(X41,X42))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 0.14/0.38  cnf(c_0_54, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.38  cnf(c_0_55, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.14/0.38  cnf(c_0_56, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.14/0.38  cnf(c_0_57, plain, (r1_xboole_0(k5_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.14/0.38  cnf(c_0_58, plain, (r1_tarski(k5_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_47, c_0_46])).
% 0.14/0.38  cnf(c_0_59, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X5,X6,X7,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.14/0.38  cnf(c_0_60, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.14/0.38  cnf(c_0_61, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.14/0.38  fof(c_0_62, plain, ![X67, X68, X69]:(~v1_relat_1(X67)|(~v1_relat_1(X68)|(~v1_relat_1(X69)|(~r1_tarski(X67,X68)|r1_tarski(k5_relat_1(X69,X67),k5_relat_1(X69,X68)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).
% 0.14/0.38  cnf(c_0_63, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.14/0.38  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.14/0.38  cnf(c_0_65, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)!=k2_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.14/0.38  cnf(c_0_66, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.14/0.38  cnf(c_0_67, plain, (v1_xboole_0(k5_xboole_0(X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 0.14/0.38  cnf(c_0_68, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X4,X5,X6,X7,X2)), inference(rw,[status(thm)],[c_0_59, c_0_39])).
% 0.14/0.38  cnf(c_0_69, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k4_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_29]), c_0_29]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.14/0.38  cnf(c_0_70, plain, (r1_tarski(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_29]), c_0_37]), c_0_38]), c_0_39])).
% 0.14/0.38  cnf(c_0_71, plain, (r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.14/0.38  cnf(c_0_72, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.14/0.38  fof(c_0_73, plain, ![X11, X12]:r1_tarski(k3_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.14/0.38  fof(c_0_74, plain, ![X63, X64]:(~r1_tarski(X63,X64)|(X63=k1_xboole_0|r1_tarski(k1_setfam_1(X64),k1_setfam_1(X63)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_setfam_1])])).
% 0.14/0.38  cnf(c_0_75, plain, (k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X1),k1_setfam_1(k4_enumset1(k4_enumset1(X3,X3,X3,X3,X3,X1),k4_enumset1(X3,X3,X3,X3,X3,X1),k4_enumset1(X3,X3,X3,X3,X3,X1),k4_enumset1(X3,X3,X3,X3,X3,X1),k4_enumset1(X3,X3,X3,X3,X3,X1),X2)))!=k4_enumset1(X3,X3,X3,X3,X3,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_26]), c_0_26]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39])).
% 0.14/0.38  cnf(c_0_76, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.14/0.38  cnf(c_0_77, plain, (r2_hidden(X1,k4_enumset1(X2,X2,X3,X4,X5,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_68])])).
% 0.14/0.38  fof(c_0_78, plain, ![X38, X39, X40]:(((r2_hidden(X38,X40)|~r1_tarski(k2_tarski(X38,X39),X40))&(r2_hidden(X39,X40)|~r1_tarski(k2_tarski(X38,X39),X40)))&(~r2_hidden(X38,X40)|~r2_hidden(X39,X40)|r1_tarski(k2_tarski(X38,X39),X40))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.14/0.38  cnf(c_0_79, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k5_relat_1(esk2_0,esk4_0))|~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k5_relat_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.14/0.38  cnf(c_0_80, plain, (r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_relat_1(X3)|~r1_tarski(X2,X3)), inference(csr,[status(thm)],[c_0_71, c_0_72])).
% 0.14/0.38  cnf(c_0_81, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.14/0.38  cnf(c_0_82, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.14/0.38  cnf(c_0_83, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.14/0.38  cnf(c_0_84, plain, (X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.14/0.38  cnf(c_0_85, plain, (k4_enumset1(X1,X1,X1,X1,X1,X2)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_46]), c_0_76]), c_0_77])])).
% 0.14/0.38  cnf(c_0_86, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.14/0.38  cnf(c_0_87, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k5_relat_1(esk2_0,esk3_0))|~r1_tarski(k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81]), c_0_82])])).
% 0.14/0.38  cnf(c_0_88, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.14/0.38  cnf(c_0_89, plain, (r1_tarski(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_29]), c_0_37]), c_0_38]), c_0_39])).
% 0.14/0.38  cnf(c_0_90, plain, (r1_tarski(k1_setfam_1(X1),X2)|~r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X2),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_46]), c_0_85])).
% 0.14/0.38  cnf(c_0_91, plain, (r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_26]), c_0_37]), c_0_38]), c_0_39])).
% 0.14/0.38  cnf(c_0_92, negated_conjecture, (~r1_tarski(k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_80]), c_0_81]), c_0_88]), c_0_89])])).
% 0.14/0.38  cnf(c_0_93, plain, (r1_tarski(k1_setfam_1(X1),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.14/0.38  cnf(c_0_94, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_77])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 95
% 0.14/0.38  # Proof object clause steps            : 51
% 0.14/0.38  # Proof object formula steps           : 44
% 0.14/0.38  # Proof object conjectures             : 12
% 0.14/0.38  # Proof object clause conjectures      : 9
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 25
% 0.14/0.38  # Proof object initial formulas used   : 22
% 0.14/0.38  # Proof object generating inferences   : 13
% 0.14/0.38  # Proof object simplifying inferences  : 74
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 22
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 41
% 0.14/0.38  # Removed in clause preprocessing      : 6
% 0.14/0.38  # Initial clauses in saturation        : 35
% 0.14/0.38  # Processed clauses                    : 106
% 0.14/0.38  # ...of these trivial                  : 2
% 0.14/0.38  # ...subsumed                          : 3
% 0.14/0.38  # ...remaining for further processing  : 101
% 0.14/0.38  # Other redundant clauses eliminated   : 39
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 1
% 0.14/0.38  # Backward-rewritten                   : 5
% 0.14/0.38  # Generated clauses                    : 328
% 0.14/0.38  # ...of the previous two non-trivial   : 236
% 0.14/0.38  # Contextual simplify-reflections      : 1
% 0.14/0.38  # Paramodulations                      : 214
% 0.14/0.38  # Factorizations                       : 80
% 0.14/0.38  # Equation resolutions                 : 39
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 54
% 0.14/0.38  #    Positive orientable unit clauses  : 18
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 3
% 0.14/0.38  #    Non-unit-clauses                  : 33
% 0.14/0.38  # Current number of unprocessed clauses: 194
% 0.14/0.38  # ...number of literals in the above   : 1299
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 47
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 283
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 189
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.14/0.38  # Unit Clause-clause subsumption calls : 53
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 35
% 0.14/0.38  # BW rewrite match successes           : 2
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 7318
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.041 s
% 0.14/0.38  # System time              : 0.004 s
% 0.14/0.38  # Total time               : 0.045 s
% 0.14/0.38  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
