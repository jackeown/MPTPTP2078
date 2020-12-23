%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:17 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 638 expanded)
%              Number of clauses        :   48 ( 239 expanded)
%              Number of leaves         :   19 ( 191 expanded)
%              Depth                    :   10
%              Number of atoms          :  261 (1275 expanded)
%              Number of equality atoms :   77 ( 599 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_orders_1,axiom,(
    ! [X1] : k1_orders_1(X1) = k7_subset_1(k1_zfmisc_1(X1),k9_setfam_1(X1),k1_tarski(k1_xboole_0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_orders_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

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

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

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

fof(t1_zfmisc_1,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t79_orders_2,axiom,(
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
             => r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

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

fof(c_0_19,plain,(
    ! [X51] : k1_orders_1(X51) = k7_subset_1(k1_zfmisc_1(X51),k9_setfam_1(X51),k1_tarski(k1_xboole_0)) ),
    inference(variable_rename,[status(thm)],[d2_orders_1])).

fof(c_0_20,plain,(
    ! [X43] : k9_setfam_1(X43) = k1_zfmisc_1(X43) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_21,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X17,X18,X19,X20] : k3_enumset1(X17,X17,X18,X19,X20) = k2_enumset1(X17,X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,negated_conjecture,(
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

fof(c_0_26,plain,(
    ! [X44,X45,X46,X47,X48,X49] :
      ( ( ~ r2_hidden(X47,X46)
        | m2_orders_2(X47,X44,X45)
        | X46 != k4_orders_2(X44,X45)
        | ~ m1_orders_1(X45,k1_orders_1(u1_struct_0(X44)))
        | v2_struct_0(X44)
        | ~ v3_orders_2(X44)
        | ~ v4_orders_2(X44)
        | ~ v5_orders_2(X44)
        | ~ l1_orders_2(X44) )
      & ( ~ m2_orders_2(X48,X44,X45)
        | r2_hidden(X48,X46)
        | X46 != k4_orders_2(X44,X45)
        | ~ m1_orders_1(X45,k1_orders_1(u1_struct_0(X44)))
        | v2_struct_0(X44)
        | ~ v3_orders_2(X44)
        | ~ v4_orders_2(X44)
        | ~ v5_orders_2(X44)
        | ~ l1_orders_2(X44) )
      & ( ~ r2_hidden(esk1_3(X44,X45,X49),X49)
        | ~ m2_orders_2(esk1_3(X44,X45,X49),X44,X45)
        | X49 = k4_orders_2(X44,X45)
        | ~ m1_orders_1(X45,k1_orders_1(u1_struct_0(X44)))
        | v2_struct_0(X44)
        | ~ v3_orders_2(X44)
        | ~ v4_orders_2(X44)
        | ~ v5_orders_2(X44)
        | ~ l1_orders_2(X44) )
      & ( r2_hidden(esk1_3(X44,X45,X49),X49)
        | m2_orders_2(esk1_3(X44,X45,X49),X44,X45)
        | X49 = k4_orders_2(X44,X45)
        | ~ m1_orders_1(X45,k1_orders_1(u1_struct_0(X44)))
        | v2_struct_0(X44)
        | ~ v3_orders_2(X44)
        | ~ v4_orders_2(X44)
        | ~ v5_orders_2(X44)
        | ~ l1_orders_2(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

cnf(c_0_27,plain,
    ( k1_orders_1(X1) = k7_subset_1(k1_zfmisc_1(X1),k9_setfam_1(X1),k1_tarski(k1_xboole_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X21,X22,X23,X24,X25] : k4_enumset1(X21,X21,X22,X23,X24,X25) = k3_enumset1(X21,X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_34,plain,(
    ! [X26,X27,X28,X29,X30,X31] : k5_enumset1(X26,X26,X27,X28,X29,X30,X31) = k4_enumset1(X26,X27,X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_35,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38] : k6_enumset1(X32,X32,X33,X34,X35,X36,X37,X38) = k5_enumset1(X32,X33,X34,X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_orders_1(esk5_0,k1_orders_1(u1_struct_0(esk4_0)))
    & k3_tarski(k4_orders_2(esk4_0,esk5_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_25])])])])).

fof(c_0_37,plain,(
    ! [X52,X53] :
      ( v2_struct_0(X52)
      | ~ v3_orders_2(X52)
      | ~ v4_orders_2(X52)
      | ~ v5_orders_2(X52)
      | ~ l1_orders_2(X52)
      | ~ m1_orders_1(X53,k1_orders_1(u1_struct_0(X52)))
      | m2_orders_2(esk2_2(X52,X53),X52,X53) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m2_orders_2])])])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X4)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | X4 != k4_orders_2(X2,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( k1_orders_1(X1) = k7_subset_1(k1_zfmisc_1(X1),k1_zfmisc_1(X1),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_40,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[t1_zfmisc_1])).

cnf(c_0_44,negated_conjecture,
    ( m1_orders_1(esk5_0,k1_orders_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | m2_orders_2(esk2_2(X1,X2),X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
    ! [X41,X42] : k1_setfam_1(k2_tarski(X41,X42)) = k3_xboole_0(X41,X42) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_47,plain,
    ( v2_struct_0(X2)
    | r2_hidden(X1,X4)
    | X4 != k4_orders_2(X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_48,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( m1_orders_1(esk5_0,k7_subset_1(k1_zfmisc_1(u1_struct_0(esk4_0)),k1_zfmisc_1(u1_struct_0(esk4_0)),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | m2_orders_2(esk2_2(X1,X2),X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_39]),c_0_40]),c_0_41]),c_0_42])).

fof(c_0_51,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_52,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_53,plain,(
    ! [X55,X56,X57] :
      ( v2_struct_0(X55)
      | ~ v3_orders_2(X55)
      | ~ v4_orders_2(X55)
      | ~ v5_orders_2(X55)
      | ~ l1_orders_2(X55)
      | ~ m1_orders_1(X56,k1_orders_1(u1_struct_0(X55)))
      | ~ m2_orders_2(X57,X55,X56)
      | r2_hidden(k1_funct_1(X56,u1_struct_0(X55)),X57) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_orders_2])])])])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,X3)
    | X3 != k4_orders_2(X1,X4)
    | ~ m2_orders_2(X2,X1,X4)
    | ~ m1_orders_1(X4,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(k1_xboole_0)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( m1_orders_1(esk5_0,k7_subset_1(k1_zfmisc_1(u1_struct_0(esk4_0)),k1_zfmisc_1(u1_struct_0(esk4_0)),k1_zfmisc_1(k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_59,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_60,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_61,plain,
    ( m2_orders_2(esk2_2(X1,X2),X1,X2)
    | v2_struct_0(X1)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(k1_xboole_0)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(rw,[status(thm)],[c_0_50,c_0_48])).

fof(c_0_62,plain,(
    ! [X39,X40] :
      ( ( k4_xboole_0(X39,k1_tarski(X40)) != X39
        | ~ r2_hidden(X40,X39) )
      & ( r2_hidden(X40,X39)
        | k4_xboole_0(X39,k1_tarski(X40)) = X39 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_64,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_30])).

fof(c_0_65,plain,(
    ! [X10] : k4_xboole_0(k1_xboole_0,X10) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m2_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_67,plain,(
    ! [X58,X59,X60] :
      ( ( X59 = k1_xboole_0
        | ~ r2_hidden(X59,X58)
        | k3_tarski(X58) != k1_xboole_0 )
      & ( esk3_1(X60) != k1_xboole_0
        | k3_tarski(X60) = k1_xboole_0 )
      & ( r2_hidden(esk3_1(X60),X60)
        | k3_tarski(X60) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k4_orders_2(esk4_0,esk5_0)
    | ~ m2_orders_2(X1,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57]),c_0_58]),c_0_59])]),c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( m2_orders_2(esk2_2(esk4_0,esk5_0),esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_55]),c_0_56]),c_0_57]),c_0_58]),c_0_59])]),c_0_60])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_74,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | k3_tarski(X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk5_0),X1)
    | X1 != k4_orders_2(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_29]),c_0_30]),c_0_71]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42])).

cnf(c_0_77,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_71]),c_0_31]),c_0_32]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_78,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(k1_xboole_0)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(rw,[status(thm)],[c_0_73,c_0_48])).

cnf(c_0_79,negated_conjecture,
    ( esk2_2(esk4_0,esk5_0) = k1_xboole_0
    | X1 != k4_orders_2(esk4_0,esk5_0)
    | k3_tarski(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk4_0,esk5_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,u1_struct_0(esk4_0)),X1)
    | ~ m2_orders_2(X1,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_55]),c_0_56]),c_0_57]),c_0_58]),c_0_59])]),c_0_60])).

cnf(c_0_83,negated_conjecture,
    ( esk2_2(esk4_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( ~ m2_orders_2(k1_xboole_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_83]),c_0_84]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___301_C18_F1_URBAN_S5PRR_S0Y
% 0.20/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.042 s
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(d2_orders_1, axiom, ![X1]:k1_orders_1(X1)=k7_subset_1(k1_zfmisc_1(X1),k9_setfam_1(X1),k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_orders_1)).
% 0.20/0.39  fof(redefinition_k9_setfam_1, axiom, ![X1]:k9_setfam_1(X1)=k1_zfmisc_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 0.20/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.39  fof(t87_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 0.20/0.39  fof(d17_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(X3=k4_orders_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>m2_orders_2(X4,X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 0.20/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.39  fof(existence_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>?[X3]:m2_orders_2(X3,X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 0.20/0.39  fof(t1_zfmisc_1, axiom, k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 0.20/0.39  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.39  fof(t79_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 0.20/0.39  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.20/0.39  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.20/0.39  fof(t91_orders_1, axiom, ![X1]:(~((?[X2]:(X2!=k1_xboole_0&r2_hidden(X2,X1))&k3_tarski(X1)=k1_xboole_0))&~((k3_tarski(X1)!=k1_xboole_0&![X2]:~((X2!=k1_xboole_0&r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 0.20/0.39  fof(c_0_19, plain, ![X51]:k1_orders_1(X51)=k7_subset_1(k1_zfmisc_1(X51),k9_setfam_1(X51),k1_tarski(k1_xboole_0)), inference(variable_rename,[status(thm)],[d2_orders_1])).
% 0.20/0.39  fof(c_0_20, plain, ![X43]:k9_setfam_1(X43)=k1_zfmisc_1(X43), inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).
% 0.20/0.39  fof(c_0_21, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.39  fof(c_0_22, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.39  fof(c_0_23, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.39  fof(c_0_24, plain, ![X17, X18, X19, X20]:k3_enumset1(X17,X17,X18,X19,X20)=k2_enumset1(X17,X18,X19,X20), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.39  fof(c_0_25, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t87_orders_2])).
% 0.20/0.39  fof(c_0_26, plain, ![X44, X45, X46, X47, X48, X49]:(((~r2_hidden(X47,X46)|m2_orders_2(X47,X44,X45)|X46!=k4_orders_2(X44,X45)|~m1_orders_1(X45,k1_orders_1(u1_struct_0(X44)))|(v2_struct_0(X44)|~v3_orders_2(X44)|~v4_orders_2(X44)|~v5_orders_2(X44)|~l1_orders_2(X44)))&(~m2_orders_2(X48,X44,X45)|r2_hidden(X48,X46)|X46!=k4_orders_2(X44,X45)|~m1_orders_1(X45,k1_orders_1(u1_struct_0(X44)))|(v2_struct_0(X44)|~v3_orders_2(X44)|~v4_orders_2(X44)|~v5_orders_2(X44)|~l1_orders_2(X44))))&((~r2_hidden(esk1_3(X44,X45,X49),X49)|~m2_orders_2(esk1_3(X44,X45,X49),X44,X45)|X49=k4_orders_2(X44,X45)|~m1_orders_1(X45,k1_orders_1(u1_struct_0(X44)))|(v2_struct_0(X44)|~v3_orders_2(X44)|~v4_orders_2(X44)|~v5_orders_2(X44)|~l1_orders_2(X44)))&(r2_hidden(esk1_3(X44,X45,X49),X49)|m2_orders_2(esk1_3(X44,X45,X49),X44,X45)|X49=k4_orders_2(X44,X45)|~m1_orders_1(X45,k1_orders_1(u1_struct_0(X44)))|(v2_struct_0(X44)|~v3_orders_2(X44)|~v4_orders_2(X44)|~v5_orders_2(X44)|~l1_orders_2(X44))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).
% 0.20/0.39  cnf(c_0_27, plain, (k1_orders_1(X1)=k7_subset_1(k1_zfmisc_1(X1),k9_setfam_1(X1),k1_tarski(k1_xboole_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  cnf(c_0_28, plain, (k9_setfam_1(X1)=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.39  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  fof(c_0_33, plain, ![X21, X22, X23, X24, X25]:k4_enumset1(X21,X21,X22,X23,X24,X25)=k3_enumset1(X21,X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.39  fof(c_0_34, plain, ![X26, X27, X28, X29, X30, X31]:k5_enumset1(X26,X26,X27,X28,X29,X30,X31)=k4_enumset1(X26,X27,X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.39  fof(c_0_35, plain, ![X32, X33, X34, X35, X36, X37, X38]:k6_enumset1(X32,X32,X33,X34,X35,X36,X37,X38)=k5_enumset1(X32,X33,X34,X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.39  fof(c_0_36, negated_conjecture, (((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&l1_orders_2(esk4_0))&(m1_orders_1(esk5_0,k1_orders_1(u1_struct_0(esk4_0)))&k3_tarski(k4_orders_2(esk4_0,esk5_0))=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_25])])])])).
% 0.20/0.39  fof(c_0_37, plain, ![X52, X53]:(v2_struct_0(X52)|~v3_orders_2(X52)|~v4_orders_2(X52)|~v5_orders_2(X52)|~l1_orders_2(X52)|~m1_orders_1(X53,k1_orders_1(u1_struct_0(X52)))|m2_orders_2(esk2_2(X52,X53),X52,X53)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m2_orders_2])])])])).
% 0.20/0.39  cnf(c_0_38, plain, (r2_hidden(X1,X4)|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|X4!=k4_orders_2(X2,X3)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_39, plain, (k1_orders_1(X1)=k7_subset_1(k1_zfmisc_1(X1),k1_zfmisc_1(X1),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.39  cnf(c_0_40, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.39  cnf(c_0_41, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.39  cnf(c_0_42, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.39  cnf(c_0_43, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(split_conjunct,[status(thm)],[t1_zfmisc_1])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (m1_orders_1(esk5_0,k1_orders_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.39  cnf(c_0_45, plain, (v2_struct_0(X1)|m2_orders_2(esk2_2(X1,X2),X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.39  fof(c_0_46, plain, ![X41, X42]:k1_setfam_1(k2_tarski(X41,X42))=k3_xboole_0(X41,X42), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.39  cnf(c_0_47, plain, (v2_struct_0(X2)|r2_hidden(X1,X4)|X4!=k4_orders_2(X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m2_orders_2(X1,X2,X3)|~m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.20/0.39  cnf(c_0_48, plain, (k1_zfmisc_1(k1_xboole_0)=k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_40]), c_0_41]), c_0_42])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (m1_orders_1(esk5_0,k7_subset_1(k1_zfmisc_1(u1_struct_0(esk4_0)),k1_zfmisc_1(u1_struct_0(esk4_0)),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.20/0.39  cnf(c_0_50, plain, (v2_struct_0(X1)|m2_orders_2(esk2_2(X1,X2),X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.20/0.39  fof(c_0_51, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.39  cnf(c_0_52, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.39  fof(c_0_53, plain, ![X55, X56, X57]:(v2_struct_0(X55)|~v3_orders_2(X55)|~v4_orders_2(X55)|~v5_orders_2(X55)|~l1_orders_2(X55)|(~m1_orders_1(X56,k1_orders_1(u1_struct_0(X55)))|(~m2_orders_2(X57,X55,X56)|r2_hidden(k1_funct_1(X56,u1_struct_0(X55)),X57)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_orders_2])])])])).
% 0.20/0.39  cnf(c_0_54, plain, (v2_struct_0(X1)|r2_hidden(X2,X3)|X3!=k4_orders_2(X1,X4)|~m2_orders_2(X2,X1,X4)|~m1_orders_1(X4,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(k1_xboole_0)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, (m1_orders_1(esk5_0,k7_subset_1(k1_zfmisc_1(u1_struct_0(esk4_0)),k1_zfmisc_1(u1_struct_0(esk4_0)),k1_zfmisc_1(k1_xboole_0)))), inference(rw,[status(thm)],[c_0_49, c_0_48])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.39  cnf(c_0_57, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.39  cnf(c_0_61, plain, (m2_orders_2(esk2_2(X1,X2),X1,X2)|v2_struct_0(X1)|~m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(k1_xboole_0)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(rw,[status(thm)],[c_0_50, c_0_48])).
% 0.20/0.39  fof(c_0_62, plain, ![X39, X40]:((k4_xboole_0(X39,k1_tarski(X40))!=X39|~r2_hidden(X40,X39))&(r2_hidden(X40,X39)|k4_xboole_0(X39,k1_tarski(X40))=X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.20/0.39  cnf(c_0_63, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.39  cnf(c_0_64, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_52, c_0_30])).
% 0.20/0.39  fof(c_0_65, plain, ![X10]:k4_xboole_0(k1_xboole_0,X10)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.20/0.39  cnf(c_0_66, plain, (v2_struct_0(X1)|r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~m2_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.39  fof(c_0_67, plain, ![X58, X59, X60]:((X59=k1_xboole_0|~r2_hidden(X59,X58)|k3_tarski(X58)!=k1_xboole_0)&((esk3_1(X60)!=k1_xboole_0|k3_tarski(X60)=k1_xboole_0)&(r2_hidden(esk3_1(X60),X60)|k3_tarski(X60)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).
% 0.20/0.39  cnf(c_0_68, negated_conjecture, (r2_hidden(X1,X2)|X2!=k4_orders_2(esk4_0,esk5_0)|~m2_orders_2(X1,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57]), c_0_58]), c_0_59])]), c_0_60])).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, (m2_orders_2(esk2_2(esk4_0,esk5_0),esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_55]), c_0_56]), c_0_57]), c_0_58]), c_0_59])]), c_0_60])).
% 0.20/0.39  cnf(c_0_70, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.39  cnf(c_0_71, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.39  cnf(c_0_72, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.39  cnf(c_0_73, plain, (v2_struct_0(X1)|r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m2_orders_2(X3,X1,X2)|~m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.20/0.39  cnf(c_0_74, plain, (X1=k1_xboole_0|~r2_hidden(X1,X2)|k3_tarski(X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.39  cnf(c_0_75, negated_conjecture, (r2_hidden(esk2_2(esk4_0,esk5_0),X1)|X1!=k4_orders_2(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.39  cnf(c_0_76, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_29]), c_0_30]), c_0_71]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42])).
% 0.20/0.39  cnf(c_0_77, plain, (k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_71]), c_0_31]), c_0_32]), c_0_40]), c_0_41]), c_0_42])).
% 0.20/0.39  cnf(c_0_78, plain, (v2_struct_0(X1)|r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)|~m2_orders_2(X3,X1,X2)|~m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)),k1_zfmisc_1(k1_xboole_0)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(rw,[status(thm)],[c_0_73, c_0_48])).
% 0.20/0.39  cnf(c_0_79, negated_conjecture, (esk2_2(esk4_0,esk5_0)=k1_xboole_0|X1!=k4_orders_2(esk4_0,esk5_0)|k3_tarski(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.39  cnf(c_0_80, negated_conjecture, (k3_tarski(k4_orders_2(esk4_0,esk5_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.39  cnf(c_0_81, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.20/0.39  cnf(c_0_82, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,u1_struct_0(esk4_0)),X1)|~m2_orders_2(X1,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_55]), c_0_56]), c_0_57]), c_0_58]), c_0_59])]), c_0_60])).
% 0.20/0.39  cnf(c_0_83, negated_conjecture, (esk2_2(esk4_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.20/0.39  cnf(c_0_84, negated_conjecture, (~m2_orders_2(k1_xboole_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.20/0.39  cnf(c_0_85, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_83]), c_0_84]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 86
% 0.20/0.39  # Proof object clause steps            : 48
% 0.20/0.39  # Proof object formula steps           : 38
% 0.20/0.39  # Proof object conjectures             : 20
% 0.20/0.39  # Proof object clause conjectures      : 17
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 25
% 0.20/0.39  # Proof object initial formulas used   : 19
% 0.20/0.39  # Proof object generating inferences   : 8
% 0.20/0.39  # Proof object simplifying inferences  : 73
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 20
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 32
% 0.20/0.39  # Removed in clause preprocessing      : 11
% 0.20/0.39  # Initial clauses in saturation        : 21
% 0.20/0.39  # Processed clauses                    : 42
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 2
% 0.20/0.39  # ...remaining for further processing  : 40
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 3
% 0.20/0.39  # Generated clauses                    : 32
% 0.20/0.39  # ...of the previous two non-trivial   : 27
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 31
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 1
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 37
% 0.20/0.39  #    Positive orientable unit clauses  : 12
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 4
% 0.20/0.39  #    Non-unit-clauses                  : 21
% 0.20/0.39  # Current number of unprocessed clauses: 5
% 0.20/0.39  # ...number of literals in the above   : 15
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 14
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 20
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 9
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.39  # Unit Clause-clause subsumption calls : 17
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 1
% 0.20/0.39  # BW rewrite match successes           : 1
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 3143
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.045 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.049 s
% 0.20/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
