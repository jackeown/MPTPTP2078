%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1178+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:03 EST 2020

% Result     : Theorem 4.92s
% Output     : CNFRefutation 4.92s
% Verified   : 
% Statistics : Number of formulae       :  101 (1405 expanded)
%              Number of clauses        :   57 ( 527 expanded)
%              Number of leaves         :   22 ( 420 expanded)
%              Depth                    :   12
%              Number of atoms          :  325 (2916 expanded)
%              Number of equality atoms :   67 (1290 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t87_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

fof(d2_orders_1,axiom,(
    ! [X1] : k1_orders_1(X1) = k7_subset_1(k1_zfmisc_1(X1),k9_setfam_1(X1),k1_tarski(k1_xboole_0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_orders_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT014+2.ax',redefinition_k9_setfam_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t72_enumset1)).

fof(t91_orders_1,axiom,(
    ! [X1] :
      ( ~ ( ? [X2] :
              ( X2 != k1_xboole_0
              & r2_hidden(X2,X1) )
          & k3_tarski(X1) = k1_xboole_0 )
      & ~ ( k3_tarski(X1) != k1_xboole_0
          & ! [X2] :
              ~ ( X2 != k1_xboole_0
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

fof(fc9_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) )
     => ~ v1_xboole_0(k4_orders_2(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t75_enumset1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d1_xboole_0)).

fof(t1_zfmisc_1,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t1_zfmisc_1)).

fof(existence_m2_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) )
     => ? [X3] : m2_orders_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

fof(t100_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t100_zfmisc_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',l1_zfmisc_1)).

fof(t82_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m2_orders_2(X3,X1,X2)
             => ! [X4] :
                  ( m2_orders_2(X4,X1,X2)
                 => ~ r1_xboole_0(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

fof(d17_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( X3 = k4_orders_2(X1,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X3)
                <=> m2_orders_2(X4,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t99_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t65_xboole_1)).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
           => k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t87_orders_2])).

fof(c_0_23,plain,(
    ! [X497] : k1_orders_1(X497) = k7_subset_1(k1_zfmisc_1(X497),k9_setfam_1(X497),k1_tarski(k1_xboole_0)) ),
    inference(variable_rename,[status(thm)],[d2_orders_1])).

fof(c_0_24,plain,(
    ! [X3593] : k9_setfam_1(X3593) = k1_zfmisc_1(X3593) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_25,plain,(
    ! [X2044] : k2_tarski(X2044,X2044) = k1_tarski(X2044) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
    ! [X2167,X2168] : k1_enumset1(X2167,X2167,X2168) = k2_tarski(X2167,X2168) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X2445,X2446,X2447] : k2_enumset1(X2445,X2445,X2446,X2447) = k1_enumset1(X2445,X2446,X2447) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X2448,X2449,X2450,X2451] : k3_enumset1(X2448,X2448,X2449,X2450,X2451) = k2_enumset1(X2448,X2449,X2450,X2451) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X267,X268,X269] :
      ( ( X268 = k1_xboole_0
        | ~ r2_hidden(X268,X267)
        | k3_tarski(X267) != k1_xboole_0 )
      & ( esk34_1(X269) != k1_xboole_0
        | k3_tarski(X269) = k1_xboole_0 )
      & ( r2_hidden(esk34_1(X269),X269)
        | k3_tarski(X269) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).

fof(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_orders_1(esk2_0,k1_orders_1(u1_struct_0(esk1_0)))
    & k3_tarski(k4_orders_2(esk1_0,esk2_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

fof(c_0_31,plain,(
    ! [X456,X457] :
      ( v2_struct_0(X456)
      | ~ v3_orders_2(X456)
      | ~ v4_orders_2(X456)
      | ~ v5_orders_2(X456)
      | ~ l1_orders_2(X456)
      | ~ m1_orders_1(X457,k1_orders_1(u1_struct_0(X456)))
      | ~ v1_xboole_0(k4_orders_2(X456,X457)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_orders_2])])])).

cnf(c_0_32,plain,
    ( k1_orders_1(X1) = k7_subset_1(k1_zfmisc_1(X1),k9_setfam_1(X1),k1_tarski(k1_xboole_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_38,plain,(
    ! [X4722,X4723,X4724,X4725,X4726] : k4_enumset1(X4722,X4722,X4723,X4724,X4725,X4726) = k3_enumset1(X4722,X4723,X4724,X4725,X4726) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_39,plain,(
    ! [X4778,X4779,X4780,X4781,X4782,X4783] : k5_enumset1(X4778,X4778,X4779,X4780,X4781,X4782,X4783) = k4_enumset1(X4778,X4779,X4780,X4781,X4782,X4783) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_40,plain,(
    ! [X4855,X4856,X4857,X4858,X4859,X4860,X4861] : k6_enumset1(X4855,X4855,X4856,X4857,X4858,X4859,X4860,X4861) = k5_enumset1(X4855,X4856,X4857,X4858,X4859,X4860,X4861) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | k3_tarski(X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk1_0,esk2_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_43,plain,(
    ! [X1072,X1073,X1074] :
      ( ( ~ v1_xboole_0(X1072)
        | ~ r2_hidden(X1073,X1072) )
      & ( r2_hidden(esk111_1(X1074),X1074)
        | v1_xboole_0(X1074) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(k4_orders_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( k1_orders_1(X1) = k7_subset_1(k1_zfmisc_1(X1),k1_zfmisc_1(X1),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_46,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[t1_zfmisc_1])).

cnf(c_0_50,negated_conjecture,
    ( m1_orders_1(esk2_0,k1_orders_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,k4_orders_2(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,plain,
    ( r2_hidden(esk111_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_xboole_0(k4_orders_2(X1,X2))
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_54,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( m1_orders_1(esk2_0,k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),k1_zfmisc_1(u1_struct_0(esk1_0)),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_45]),c_0_46]),c_0_47]),c_0_48])).

fof(c_0_56,plain,(
    ! [X468,X469] :
      ( v2_struct_0(X468)
      | ~ v3_orders_2(X468)
      | ~ v4_orders_2(X468)
      | ~ v5_orders_2(X468)
      | ~ l1_orders_2(X468)
      | ~ m1_orders_1(X469,k1_orders_1(u1_struct_0(X468)))
      | m2_orders_2(esk90_2(X468,X469),X468,X469) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m2_orders_2])])])])).

fof(c_0_57,plain,(
    ! [X294] : r1_tarski(X294,k1_zfmisc_1(k3_tarski(X294))) ),
    inference(variable_rename,[status(thm)],[t100_zfmisc_1])).

fof(c_0_58,plain,(
    ! [X1296,X1297] :
      ( ( ~ r1_tarski(k1_tarski(X1296),X1297)
        | r2_hidden(X1296,X1297) )
      & ( ~ r2_hidden(X1296,X1297)
        | r1_tarski(k1_tarski(X1296),X1297) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_59,negated_conjecture,
    ( esk111_1(k4_orders_2(esk1_0,esk2_0)) = k1_xboole_0
    | v1_xboole_0(k4_orders_2(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(k1_xboole_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(k4_orders_2(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( m1_orders_1(esk2_0,k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),k1_zfmisc_1(u1_struct_0(esk1_0)),k1_zfmisc_1(k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_55,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_63,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_64,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_65,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_66,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_67,plain,(
    ! [X485,X486,X487,X488] :
      ( v2_struct_0(X485)
      | ~ v3_orders_2(X485)
      | ~ v4_orders_2(X485)
      | ~ v5_orders_2(X485)
      | ~ l1_orders_2(X485)
      | ~ m1_orders_1(X486,k1_orders_1(u1_struct_0(X485)))
      | ~ m2_orders_2(X487,X485,X486)
      | ~ m2_orders_2(X488,X485,X486)
      | ~ r1_xboole_0(X487,X488) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t82_orders_2])])])])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | m2_orders_2(esk90_2(X1,X2),X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_69,plain,(
    ! [X449,X450,X451,X452,X453,X454] :
      ( ( ~ r2_hidden(X452,X451)
        | m2_orders_2(X452,X449,X450)
        | X451 != k4_orders_2(X449,X450)
        | ~ m1_orders_1(X450,k1_orders_1(u1_struct_0(X449)))
        | v2_struct_0(X449)
        | ~ v3_orders_2(X449)
        | ~ v4_orders_2(X449)
        | ~ v5_orders_2(X449)
        | ~ l1_orders_2(X449) )
      & ( ~ m2_orders_2(X453,X449,X450)
        | r2_hidden(X453,X451)
        | X451 != k4_orders_2(X449,X450)
        | ~ m1_orders_1(X450,k1_orders_1(u1_struct_0(X449)))
        | v2_struct_0(X449)
        | ~ v3_orders_2(X449)
        | ~ v4_orders_2(X449)
        | ~ v5_orders_2(X449)
        | ~ l1_orders_2(X449) )
      & ( ~ r2_hidden(esk87_3(X449,X450,X454),X454)
        | ~ m2_orders_2(esk87_3(X449,X450,X454),X449,X450)
        | X454 = k4_orders_2(X449,X450)
        | ~ m1_orders_1(X450,k1_orders_1(u1_struct_0(X449)))
        | v2_struct_0(X449)
        | ~ v3_orders_2(X449)
        | ~ v4_orders_2(X449)
        | ~ v5_orders_2(X449)
        | ~ l1_orders_2(X449) )
      & ( r2_hidden(esk87_3(X449,X450,X454),X454)
        | m2_orders_2(esk87_3(X449,X450,X454),X449,X450)
        | X454 = k4_orders_2(X449,X450)
        | ~ m1_orders_1(X450,k1_orders_1(u1_struct_0(X449)))
        | v2_struct_0(X449)
        | ~ v3_orders_2(X449)
        | ~ v4_orders_2(X449)
        | ~ v5_orders_2(X449)
        | ~ l1_orders_2(X449) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

fof(c_0_70,plain,(
    ! [X1627,X1628] :
      ( ( r1_tarski(X1627,X1628)
        | X1627 != X1628 )
      & ( r1_tarski(X1628,X1627)
        | X1627 != X1628 )
      & ( ~ r1_tarski(X1627,X1628)
        | ~ r1_tarski(X1628,X1627)
        | X1627 = X1628 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_72,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_73,negated_conjecture,
    ( v1_xboole_0(k4_orders_2(esk1_0,esk2_0))
    | r2_hidden(k1_xboole_0,k4_orders_2(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_59])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_xboole_0(k4_orders_2(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63]),c_0_64]),c_0_65])]),c_0_66])).

cnf(c_0_75,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m2_orders_2(X4,X1,X2)
    | ~ r1_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | m2_orders_2(esk90_2(X1,X2),X1,X2)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X4)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | X4 != k4_orders_2(X2,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_78,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k4_orders_2(esk1_0,esk2_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_42])).

cnf(c_0_80,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k4_orders_2(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_82,plain,
    ( v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_xboole_0(X3,X4)
    | ~ m2_orders_2(X4,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_83,plain,
    ( m2_orders_2(esk90_2(X1,X2),X1,X2)
    | v2_struct_0(X1)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(k1_xboole_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(rw,[status(thm)],[c_0_76,c_0_54])).

fof(c_0_84,plain,(
    ! [X322] : k3_tarski(k1_zfmisc_1(X322)) = X322 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_85,plain,
    ( v2_struct_0(X2)
    | r2_hidden(X1,X4)
    | X4 != k4_orders_2(X2,X3)
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_86,negated_conjecture,
    ( k4_orders_2(esk1_0,esk2_0) = k1_zfmisc_1(k1_xboole_0)
    | ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k4_orders_2(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(k1_xboole_0),k4_orders_2(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_54])).

cnf(c_0_88,plain,
    ( v2_struct_0(X1)
    | ~ m2_orders_2(X2,X1,X3)
    | ~ m2_orders_2(X4,X1,X3)
    | ~ m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(k1_xboole_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ r1_xboole_0(X4,X2) ),
    inference(rw,[status(thm)],[c_0_82,c_0_54])).

cnf(c_0_89,negated_conjecture,
    ( m2_orders_2(esk90_2(esk1_0,esk2_0),esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_61]),c_0_62]),c_0_63]),c_0_64]),c_0_65])]),c_0_66])).

cnf(c_0_90,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_91,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k4_orders_2(X1,X3))
    | ~ m2_orders_2(X2,X1,X3)
    | ~ m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(k1_xboole_0)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_54])])).

cnf(c_0_92,negated_conjecture,
    ( k4_orders_2(esk1_0,esk2_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_93,negated_conjecture,
    ( ~ m2_orders_2(X1,esk1_0,esk2_0)
    | ~ r1_xboole_0(X1,esk90_2(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_61]),c_0_62]),c_0_63]),c_0_64]),c_0_65])]),c_0_66])).

cnf(c_0_94,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_90])])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk90_2(esk1_0,esk2_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_89]),c_0_92]),c_0_61]),c_0_62]),c_0_63]),c_0_64]),c_0_65])]),c_0_66])).

fof(c_0_96,plain,(
    ! [X44] : r1_xboole_0(X44,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_97,negated_conjecture,
    ( ~ r1_xboole_0(esk90_2(esk1_0,esk2_0),esk90_2(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_89])).

cnf(c_0_98,negated_conjecture,
    ( esk90_2(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98]),c_0_98]),c_0_99])]),
    [proof]).
%------------------------------------------------------------------------------
