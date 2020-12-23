%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:00 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 245 expanded)
%              Number of clauses        :   57 ( 118 expanded)
%              Number of leaves         :   21 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  199 ( 507 expanded)
%              Number of equality atoms :   62 ( 200 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t82_enumset1,axiom,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t80_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_enumset1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(t82_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

fof(t38_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(dt_k1_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(fc13_subset_1,axiom,(
    ! [X1] : v1_xboole_0(k1_subset_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(t57_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ! [X3] :
          ( m1_subset_1(X3,X1)
         => ! [X4] :
              ( m1_subset_1(X4,X1)
             => ( X1 != k1_xboole_0
               => m1_subset_1(k1_enumset1(X2,X3,X4),k1_zfmisc_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_subset_1)).

fof(t93_enumset1,axiom,(
    ! [X1,X2,X3] : k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_enumset1)).

fof(t61_setfam_1,conjecture,(
    ! [X1] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t91_enumset1,axiom,(
    ! [X1] : k4_enumset1(X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_enumset1)).

fof(t81_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_enumset1)).

fof(c_0_21,plain,(
    ! [X49,X50,X51] :
      ( ( r2_hidden(X49,X50)
        | ~ r2_hidden(X49,k4_xboole_0(X50,k1_tarski(X51))) )
      & ( X49 != X51
        | ~ r2_hidden(X49,k4_xboole_0(X50,k1_tarski(X51))) )
      & ( ~ r2_hidden(X49,X50)
        | X49 = X51
        | r2_hidden(X49,k4_xboole_0(X50,k1_tarski(X51))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_22,plain,(
    ! [X30] : k2_enumset1(X30,X30,X30,X30) = k1_tarski(X30) ),
    inference(variable_rename,[status(thm)],[t82_enumset1])).

fof(c_0_23,plain,(
    ! [X15,X16,X17,X18] : k3_enumset1(X15,X15,X16,X17,X18) = k2_enumset1(X15,X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X19,X20,X21,X22,X23] : k5_enumset1(X19,X19,X19,X20,X21,X22,X23) = k3_enumset1(X19,X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t80_enumset1])).

fof(c_0_25,plain,(
    ! [X13,X14] :
      ( ~ v1_xboole_0(X13)
      | X13 = X14
      | ~ v1_xboole_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_26,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X10] :
      ( ( r1_xboole_0(X10,X10)
        | X10 != k1_xboole_0 )
      & ( X10 = k1_xboole_0
        | ~ r1_xboole_0(X10,X10) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

fof(c_0_31,plain,(
    ! [X11,X12] : r1_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X12,X11)) ),
    inference(variable_rename,[status(thm)],[t82_xboole_1])).

fof(c_0_32,plain,(
    ! [X54,X55] :
      ( ( ~ r1_tarski(X55,k3_subset_1(X54,X55))
        | X55 = k1_subset_1(X54)
        | ~ m1_subset_1(X55,k1_zfmisc_1(X54)) )
      & ( X55 != k1_subset_1(X54)
        | r1_tarski(X55,k3_subset_1(X54,X55))
        | ~ m1_subset_1(X55,k1_zfmisc_1(X54)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_subset_1])])])).

fof(c_0_33,plain,(
    ! [X52] : m1_subset_1(k1_subset_1(X52),k1_zfmisc_1(X52)) ),
    inference(variable_rename,[status(thm)],[dt_k1_subset_1])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_36,plain,(
    ! [X53] : v1_xboole_0(k1_subset_1(X53)) ),
    inference(variable_rename,[status(thm)],[fc13_subset_1])).

cnf(c_0_37,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X1))
    | X1 != k1_subset_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( X1 = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( v1_xboole_0(k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,plain,(
    ! [X45,X46,X47,X48] :
      ( ( ~ r1_xboole_0(X45,X46)
        | r1_xboole_0(k2_zfmisc_1(X45,X47),k2_zfmisc_1(X46,X48)) )
      & ( ~ r1_xboole_0(X47,X48)
        | r1_xboole_0(k2_zfmisc_1(X45,X47),k2_zfmisc_1(X46,X48)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_46,plain,(
    ! [X7,X8,X9] :
      ( ( r1_tarski(X7,X8)
        | ~ r1_tarski(X7,k4_xboole_0(X8,X9)) )
      & ( r1_xboole_0(X7,X9)
        | ~ r1_tarski(X7,k4_xboole_0(X8,X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_49,plain,(
    ! [X35,X36,X37,X38,X39,X40] :
      ( ( ~ r2_hidden(X37,X36)
        | r1_tarski(X37,X35)
        | X36 != k1_zfmisc_1(X35) )
      & ( ~ r1_tarski(X38,X35)
        | r2_hidden(X38,X36)
        | X36 != k1_zfmisc_1(X35) )
      & ( ~ r2_hidden(esk1_2(X39,X40),X40)
        | ~ r1_tarski(esk1_2(X39,X40),X39)
        | X40 = k1_zfmisc_1(X39) )
      & ( r2_hidden(esk1_2(X39,X40),X40)
        | r1_tarski(esk1_2(X39,X40),X39)
        | X40 = k1_zfmisc_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_50,plain,(
    ! [X42,X43,X44] :
      ( ( r1_tarski(k2_zfmisc_1(X42,X44),k2_zfmisc_1(X43,X44))
        | ~ r1_tarski(X42,X43) )
      & ( r1_tarski(k2_zfmisc_1(X44,X42),k2_zfmisc_1(X44,X43))
        | ~ r1_tarski(X42,X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_subset_1(X1),k3_subset_1(X1,k1_subset_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_40]),c_0_41])])).

cnf(c_0_52,plain,
    ( k1_subset_1(X1) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,plain,
    ( r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_tarski(esk1_2(X1,X2),X1)
    | X2 = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_58,plain,(
    ! [X57,X58,X59,X60] :
      ( ~ m1_subset_1(X58,X57)
      | ~ m1_subset_1(X59,X57)
      | ~ m1_subset_1(X60,X57)
      | X57 = k1_xboole_0
      | m1_subset_1(k1_enumset1(X58,X59,X60),k1_zfmisc_1(X57)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_subset_1])])])).

fof(c_0_59,plain,(
    ! [X32,X33,X34] : k6_enumset1(X32,X32,X32,X32,X32,X32,X33,X34) = k1_enumset1(X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t93_enumset1])).

cnf(c_0_60,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( r1_tarski(o_0_0_xboole_0,k3_subset_1(X1,o_0_0_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_52])).

cnf(c_0_62,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0),k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_48])).

cnf(c_0_65,plain,
    ( k1_zfmisc_1(X1) = k1_xboole_0
    | r1_tarski(esk1_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_66,negated_conjecture,(
    ~ ! [X1] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(assume_negation,[status(cth)],[t61_setfam_1])).

cnf(c_0_67,plain,
    ( X2 = k1_xboole_0
    | m1_subset_1(k1_enumset1(X1,X3,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(X3,X2)
    | ~ m1_subset_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_69,plain,(
    ! [X56] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X56)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_71,plain,
    ( r1_tarski(k2_zfmisc_1(o_0_0_xboole_0,X1),k2_zfmisc_1(k3_subset_1(X2,o_0_0_xboole_0),X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_72,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_62])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_48])).

cnf(c_0_74,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | r1_xboole_0(esk1_2(k1_xboole_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

fof(c_0_75,negated_conjecture,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_66])])])).

fof(c_0_76,plain,(
    ! [X31] : k4_enumset1(X31,X31,X31,X31,X31,X31) = k1_tarski(X31) ),
    inference(variable_rename,[status(thm)],[t91_enumset1])).

fof(c_0_77,plain,(
    ! [X24,X25,X26,X27,X28,X29] : k6_enumset1(X24,X24,X24,X25,X26,X27,X28,X29) = k4_enumset1(X24,X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t81_enumset1])).

cnf(c_0_78,plain,
    ( X2 = k1_xboole_0
    | m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X3,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,X2)
    | ~ m1_subset_1(X3,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_79,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_81,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_72])).

cnf(c_0_82,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | r1_tarski(esk1_2(k1_xboole_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_65])).

cnf(c_0_83,plain,
    ( esk1_2(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_74])).

cnf(c_0_84,negated_conjecture,
    ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_85,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_86,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_87,plain,
    ( k1_zfmisc_1(X1) = k1_xboole_0
    | m1_subset_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_88,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_89,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( ~ m1_subset_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_91,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_27]),c_0_28]),c_0_29]),c_0_86])).

cnf(c_0_92,plain,
    ( k1_zfmisc_1(X1) = k1_xboole_0
    | m1_subset_1(k6_enumset1(X2,X2,X2,X2,X2,X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_79])).

cnf(c_0_93,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_56])).

cnf(c_0_94,negated_conjecture,
    ( ~ m1_subset_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_95,plain,
    ( k1_zfmisc_1(X1) = k1_xboole_0
    | m1_subset_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_79])).

cnf(c_0_96,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( k1_zfmisc_1(esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:39:59 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.21/0.41  # and selection function GSelectMinInfpos.
% 0.21/0.41  #
% 0.21/0.41  # Preprocessing time       : 0.027 s
% 0.21/0.41  # Presaturation interreduction done
% 0.21/0.41  
% 0.21/0.41  # Proof found!
% 0.21/0.41  # SZS status Theorem
% 0.21/0.41  # SZS output start CNFRefutation
% 0.21/0.41  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.21/0.41  fof(t82_enumset1, axiom, ![X1]:k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 0.21/0.41  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.41  fof(t80_enumset1, axiom, ![X1, X2, X3, X4, X5]:k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_enumset1)).
% 0.21/0.41  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 0.21/0.41  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.21/0.41  fof(t82_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_xboole_1)).
% 0.21/0.41  fof(t38_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 0.21/0.41  fof(dt_k1_subset_1, axiom, ![X1]:m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 0.21/0.41  fof(dt_o_0_0_xboole_0, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 0.21/0.41  fof(fc13_subset_1, axiom, ![X1]:v1_xboole_0(k1_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_subset_1)).
% 0.21/0.41  fof(t127_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 0.21/0.41  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.21/0.41  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.21/0.41  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 0.21/0.41  fof(t57_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m1_subset_1(X4,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k1_enumset1(X2,X3,X4),k1_zfmisc_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_subset_1)).
% 0.21/0.41  fof(t93_enumset1, axiom, ![X1, X2, X3]:k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_enumset1)).
% 0.21/0.41  fof(t61_setfam_1, conjecture, ![X1]:m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 0.21/0.41  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.21/0.41  fof(t91_enumset1, axiom, ![X1]:k4_enumset1(X1,X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_enumset1)).
% 0.21/0.41  fof(t81_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_enumset1)).
% 0.21/0.41  fof(c_0_21, plain, ![X49, X50, X51]:(((r2_hidden(X49,X50)|~r2_hidden(X49,k4_xboole_0(X50,k1_tarski(X51))))&(X49!=X51|~r2_hidden(X49,k4_xboole_0(X50,k1_tarski(X51)))))&(~r2_hidden(X49,X50)|X49=X51|r2_hidden(X49,k4_xboole_0(X50,k1_tarski(X51))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.21/0.41  fof(c_0_22, plain, ![X30]:k2_enumset1(X30,X30,X30,X30)=k1_tarski(X30), inference(variable_rename,[status(thm)],[t82_enumset1])).
% 0.21/0.41  fof(c_0_23, plain, ![X15, X16, X17, X18]:k3_enumset1(X15,X15,X16,X17,X18)=k2_enumset1(X15,X16,X17,X18), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.41  fof(c_0_24, plain, ![X19, X20, X21, X22, X23]:k5_enumset1(X19,X19,X19,X20,X21,X22,X23)=k3_enumset1(X19,X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t80_enumset1])).
% 0.21/0.41  fof(c_0_25, plain, ![X13, X14]:(~v1_xboole_0(X13)|X13=X14|~v1_xboole_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.21/0.41  cnf(c_0_26, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.41  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.41  cnf(c_0_28, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.41  cnf(c_0_29, plain, (k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.41  fof(c_0_30, plain, ![X10]:((r1_xboole_0(X10,X10)|X10!=k1_xboole_0)&(X10=k1_xboole_0|~r1_xboole_0(X10,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.21/0.41  fof(c_0_31, plain, ![X11, X12]:r1_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[t82_xboole_1])).
% 0.21/0.41  fof(c_0_32, plain, ![X54, X55]:((~r1_tarski(X55,k3_subset_1(X54,X55))|X55=k1_subset_1(X54)|~m1_subset_1(X55,k1_zfmisc_1(X54)))&(X55!=k1_subset_1(X54)|r1_tarski(X55,k3_subset_1(X54,X55))|~m1_subset_1(X55,k1_zfmisc_1(X54)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_subset_1])])])).
% 0.21/0.41  fof(c_0_33, plain, ![X52]:m1_subset_1(k1_subset_1(X52),k1_zfmisc_1(X52)), inference(variable_rename,[status(thm)],[dt_k1_subset_1])).
% 0.21/0.41  cnf(c_0_34, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.41  cnf(c_0_35, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).
% 0.21/0.41  fof(c_0_36, plain, ![X53]:v1_xboole_0(k1_subset_1(X53)), inference(variable_rename,[status(thm)],[fc13_subset_1])).
% 0.21/0.41  cnf(c_0_37, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])).
% 0.21/0.41  cnf(c_0_38, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.41  cnf(c_0_39, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.41  cnf(c_0_40, plain, (r1_tarski(X1,k3_subset_1(X2,X1))|X1!=k1_subset_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.41  cnf(c_0_41, plain, (m1_subset_1(k1_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.41  cnf(c_0_42, plain, (X1=o_0_0_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.41  cnf(c_0_43, plain, (v1_xboole_0(k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.41  fof(c_0_44, plain, ![X45, X46, X47, X48]:((~r1_xboole_0(X45,X46)|r1_xboole_0(k2_zfmisc_1(X45,X47),k2_zfmisc_1(X46,X48)))&(~r1_xboole_0(X47,X48)|r1_xboole_0(k2_zfmisc_1(X45,X47),k2_zfmisc_1(X46,X48)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).
% 0.21/0.41  cnf(c_0_45, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.41  fof(c_0_46, plain, ![X7, X8, X9]:((r1_tarski(X7,X8)|~r1_tarski(X7,k4_xboole_0(X8,X9)))&(r1_xboole_0(X7,X9)|~r1_tarski(X7,k4_xboole_0(X8,X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.21/0.41  cnf(c_0_47, plain, (~r2_hidden(X1,k4_xboole_0(X2,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))), inference(er,[status(thm)],[c_0_37])).
% 0.21/0.41  cnf(c_0_48, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.41  fof(c_0_49, plain, ![X35, X36, X37, X38, X39, X40]:(((~r2_hidden(X37,X36)|r1_tarski(X37,X35)|X36!=k1_zfmisc_1(X35))&(~r1_tarski(X38,X35)|r2_hidden(X38,X36)|X36!=k1_zfmisc_1(X35)))&((~r2_hidden(esk1_2(X39,X40),X40)|~r1_tarski(esk1_2(X39,X40),X39)|X40=k1_zfmisc_1(X39))&(r2_hidden(esk1_2(X39,X40),X40)|r1_tarski(esk1_2(X39,X40),X39)|X40=k1_zfmisc_1(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.21/0.41  fof(c_0_50, plain, ![X42, X43, X44]:((r1_tarski(k2_zfmisc_1(X42,X44),k2_zfmisc_1(X43,X44))|~r1_tarski(X42,X43))&(r1_tarski(k2_zfmisc_1(X44,X42),k2_zfmisc_1(X44,X43))|~r1_tarski(X42,X43))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 0.21/0.41  cnf(c_0_51, plain, (r1_tarski(k1_subset_1(X1),k3_subset_1(X1,k1_subset_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_40]), c_0_41])])).
% 0.21/0.41  cnf(c_0_52, plain, (k1_subset_1(X1)=o_0_0_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.41  cnf(c_0_53, plain, (r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.41  cnf(c_0_54, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[c_0_45])).
% 0.21/0.41  cnf(c_0_55, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.41  cnf(c_0_56, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.21/0.41  cnf(c_0_57, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_tarski(esk1_2(X1,X2),X1)|X2=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.41  fof(c_0_58, plain, ![X57, X58, X59, X60]:(~m1_subset_1(X58,X57)|(~m1_subset_1(X59,X57)|(~m1_subset_1(X60,X57)|(X57=k1_xboole_0|m1_subset_1(k1_enumset1(X58,X59,X60),k1_zfmisc_1(X57)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_subset_1])])])).
% 0.21/0.41  fof(c_0_59, plain, ![X32, X33, X34]:k6_enumset1(X32,X32,X32,X32,X32,X32,X33,X34)=k1_enumset1(X32,X33,X34), inference(variable_rename,[status(thm)],[t93_enumset1])).
% 0.21/0.41  cnf(c_0_60, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.41  cnf(c_0_61, plain, (r1_tarski(o_0_0_xboole_0,k3_subset_1(X1,o_0_0_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_52])).
% 0.21/0.41  cnf(c_0_62, plain, (r1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0),k2_zfmisc_1(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.41  cnf(c_0_63, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.41  cnf(c_0_64, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_55, c_0_48])).
% 0.21/0.41  cnf(c_0_65, plain, (k1_zfmisc_1(X1)=k1_xboole_0|r1_tarski(esk1_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.41  fof(c_0_66, negated_conjecture, ~(![X1]:m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(assume_negation,[status(cth)],[t61_setfam_1])).
% 0.21/0.41  cnf(c_0_67, plain, (X2=k1_xboole_0|m1_subset_1(k1_enumset1(X1,X3,X4),k1_zfmisc_1(X2))|~m1_subset_1(X1,X2)|~m1_subset_1(X3,X2)|~m1_subset_1(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.21/0.41  cnf(c_0_68, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.21/0.41  fof(c_0_69, plain, ![X56]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X56)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.21/0.41  cnf(c_0_70, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.41  cnf(c_0_71, plain, (r1_tarski(k2_zfmisc_1(o_0_0_xboole_0,X1),k2_zfmisc_1(k3_subset_1(X2,o_0_0_xboole_0),X1))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.21/0.41  cnf(c_0_72, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_62])).
% 0.21/0.41  cnf(c_0_73, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_63, c_0_48])).
% 0.21/0.41  cnf(c_0_74, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0|r1_xboole_0(esk1_2(k1_xboole_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.21/0.41  fof(c_0_75, negated_conjecture, ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_66])])])).
% 0.21/0.41  fof(c_0_76, plain, ![X31]:k4_enumset1(X31,X31,X31,X31,X31,X31)=k1_tarski(X31), inference(variable_rename,[status(thm)],[t91_enumset1])).
% 0.21/0.41  fof(c_0_77, plain, ![X24, X25, X26, X27, X28, X29]:k6_enumset1(X24,X24,X24,X25,X26,X27,X28,X29)=k4_enumset1(X24,X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t81_enumset1])).
% 0.21/0.41  cnf(c_0_78, plain, (X2=k1_xboole_0|m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X3,X4),k1_zfmisc_1(X2))|~m1_subset_1(X4,X2)|~m1_subset_1(X3,X2)|~m1_subset_1(X1,X2)), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.21/0.41  cnf(c_0_79, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.21/0.41  cnf(c_0_80, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_70])).
% 0.21/0.41  cnf(c_0_81, plain, (r1_tarski(k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_72])).
% 0.21/0.41  cnf(c_0_82, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0|r1_tarski(esk1_2(k1_xboole_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_73, c_0_65])).
% 0.21/0.41  cnf(c_0_83, plain, (esk1_2(k1_xboole_0,k1_xboole_0)=k1_xboole_0|k1_zfmisc_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_74])).
% 0.21/0.41  cnf(c_0_84, negated_conjecture, (~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.21/0.41  cnf(c_0_85, plain, (k4_enumset1(X1,X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.21/0.41  cnf(c_0_86, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.21/0.41  cnf(c_0_87, plain, (k1_zfmisc_1(X1)=k1_xboole_0|m1_subset_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.21/0.41  cnf(c_0_88, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.21/0.41  cnf(c_0_89, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0|r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.21/0.41  cnf(c_0_90, negated_conjecture, (~m1_subset_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_27]), c_0_28]), c_0_29])).
% 0.21/0.41  cnf(c_0_91, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_27]), c_0_28]), c_0_29]), c_0_86])).
% 0.21/0.41  cnf(c_0_92, plain, (k1_zfmisc_1(X1)=k1_xboole_0|m1_subset_1(k6_enumset1(X2,X2,X2,X2,X2,X2,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_87, c_0_79])).
% 0.21/0.41  cnf(c_0_93, plain, (r1_tarski(k1_xboole_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_56])).
% 0.21/0.41  cnf(c_0_94, negated_conjecture, (~m1_subset_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(rw,[status(thm)],[c_0_90, c_0_91])).
% 0.21/0.41  cnf(c_0_95, plain, (k1_zfmisc_1(X1)=k1_xboole_0|m1_subset_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_92, c_0_79])).
% 0.21/0.41  cnf(c_0_96, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_80, c_0_93])).
% 0.21/0.41  cnf(c_0_97, negated_conjecture, (k1_zfmisc_1(esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.21/0.41  cnf(c_0_98, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_56]), ['proof']).
% 0.21/0.41  # SZS output end CNFRefutation
% 0.21/0.41  # Proof object total steps             : 99
% 0.21/0.41  # Proof object clause steps            : 57
% 0.21/0.41  # Proof object formula steps           : 42
% 0.21/0.41  # Proof object conjectures             : 8
% 0.21/0.41  # Proof object clause conjectures      : 5
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 24
% 0.21/0.41  # Proof object initial formulas used   : 21
% 0.21/0.41  # Proof object generating inferences   : 23
% 0.21/0.41  # Proof object simplifying inferences  : 23
% 0.21/0.41  # Training examples: 0 positive, 0 negative
% 0.21/0.41  # Parsed axioms                        : 22
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 32
% 0.21/0.41  # Removed in clause preprocessing      : 5
% 0.21/0.41  # Initial clauses in saturation        : 27
% 0.21/0.41  # Processed clauses                    : 412
% 0.21/0.41  # ...of these trivial                  : 6
% 0.21/0.41  # ...subsumed                          : 146
% 0.21/0.41  # ...remaining for further processing  : 260
% 0.21/0.41  # Other redundant clauses eliminated   : 5
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 40
% 0.21/0.41  # Backward-rewritten                   : 27
% 0.21/0.41  # Generated clauses                    : 2056
% 0.21/0.41  # ...of the previous two non-trivial   : 807
% 0.21/0.41  # Contextual simplify-reflections      : 0
% 0.21/0.41  # Paramodulations                      : 2047
% 0.21/0.41  # Factorizations                       : 4
% 0.21/0.41  # Equation resolutions                 : 5
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 161
% 0.21/0.41  #    Positive orientable unit clauses  : 45
% 0.21/0.41  #    Positive unorientable unit clauses: 1
% 0.21/0.41  #    Negative unit clauses             : 3
% 0.21/0.41  #    Non-unit-clauses                  : 112
% 0.21/0.41  # Current number of unprocessed clauses: 356
% 0.21/0.41  # ...number of literals in the above   : 991
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 99
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 3225
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 2295
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 170
% 0.21/0.41  # Unit Clause-clause subsumption calls : 163
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 193
% 0.21/0.41  # BW rewrite match successes           : 20
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 24403
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.057 s
% 0.21/0.41  # System time              : 0.006 s
% 0.21/0.41  # Total time               : 0.063 s
% 0.21/0.41  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
