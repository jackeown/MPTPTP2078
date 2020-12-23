%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:53 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 344 expanded)
%              Number of clauses        :   51 ( 121 expanded)
%              Number of leaves         :   16 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          :  376 (2666 expanded)
%              Number of equality atoms :  104 ( 437 expanded)
%              Maximal formula depth    :   47 (   5 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d5_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( ~ r1_tsep_1(X2,X3)
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & v1_pre_topc(X4)
                      & m1_pre_topc(X4,X1) )
                   => ( X4 = k2_tsep_1(X1,X2,X3)
                    <=> u1_struct_0(X4) = k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(dt_k2_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
        & v1_pre_topc(k2_tsep_1(X1,X2,X3))
        & m1_pre_topc(k2_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(t17_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( ~ r1_tsep_1(X2,X3)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(k2_tsep_1(X1,X2,X3)))
                   => ( ? [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                          & X5 = X4 )
                      & ? [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                          & X5 = X4 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tmap_1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(d6_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( X9 = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X10 != X1
              & X10 != X2
              & X10 != X3
              & X10 != X4
              & X10 != X5
              & X10 != X6
              & X10 != X7
              & X10 != X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t4_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
              <=> m1_pre_topc(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(t55_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(c_0_16,plain,(
    ! [X61,X62] : k1_setfam_1(k2_tarski(X61,X62)) = k3_xboole_0(X61,X62) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_17,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X70,X71,X72,X73] :
      ( ( X73 != k2_tsep_1(X70,X71,X72)
        | u1_struct_0(X73) = k3_xboole_0(u1_struct_0(X71),u1_struct_0(X72))
        | v2_struct_0(X73)
        | ~ v1_pre_topc(X73)
        | ~ m1_pre_topc(X73,X70)
        | r1_tsep_1(X71,X72)
        | v2_struct_0(X72)
        | ~ m1_pre_topc(X72,X70)
        | v2_struct_0(X71)
        | ~ m1_pre_topc(X71,X70)
        | v2_struct_0(X70)
        | ~ l1_pre_topc(X70) )
      & ( u1_struct_0(X73) != k3_xboole_0(u1_struct_0(X71),u1_struct_0(X72))
        | X73 = k2_tsep_1(X70,X71,X72)
        | v2_struct_0(X73)
        | ~ v1_pre_topc(X73)
        | ~ m1_pre_topc(X73,X70)
        | r1_tsep_1(X71,X72)
        | v2_struct_0(X72)
        | ~ m1_pre_topc(X72,X70)
        | v2_struct_0(X71)
        | ~ m1_pre_topc(X71,X70)
        | v2_struct_0(X70)
        | ~ l1_pre_topc(X70) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X18,X19,X20,X21] : k3_enumset1(X18,X18,X19,X20,X21) = k2_enumset1(X18,X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_23,plain,(
    ! [X22,X23,X24,X25,X26] : k4_enumset1(X22,X22,X23,X24,X25,X26) = k3_enumset1(X22,X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_24,plain,(
    ! [X27,X28,X29,X30,X31,X32] : k5_enumset1(X27,X27,X28,X29,X30,X31,X32) = k4_enumset1(X27,X28,X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_25,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39] : k6_enumset1(X33,X33,X34,X35,X36,X37,X38,X39) = k5_enumset1(X33,X34,X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_26,plain,
    ( u1_struct_0(X1) = k3_xboole_0(u1_struct_0(X3),u1_struct_0(X4))
    | v2_struct_0(X1)
    | r1_tsep_1(X3,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | X1 != k2_tsep_1(X2,X3,X4)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X74,X75,X76] :
      ( ( ~ v2_struct_0(k2_tsep_1(X74,X75,X76))
        | v2_struct_0(X74)
        | ~ l1_pre_topc(X74)
        | v2_struct_0(X75)
        | ~ m1_pre_topc(X75,X74)
        | v2_struct_0(X76)
        | ~ m1_pre_topc(X76,X74) )
      & ( v1_pre_topc(k2_tsep_1(X74,X75,X76))
        | v2_struct_0(X74)
        | ~ l1_pre_topc(X74)
        | v2_struct_0(X75)
        | ~ m1_pre_topc(X75,X74)
        | v2_struct_0(X76)
        | ~ m1_pre_topc(X76,X74) )
      & ( m1_pre_topc(k2_tsep_1(X74,X75,X76),X74)
        | v2_struct_0(X74)
        | ~ l1_pre_topc(X74)
        | v2_struct_0(X75)
        | ~ m1_pre_topc(X75,X74)
        | v2_struct_0(X76)
        | ~ m1_pre_topc(X76,X74) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

fof(c_0_34,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ( ~ r1_tsep_1(X2,X3)
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(k2_tsep_1(X1,X2,X3)))
                     => ( ? [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                            & X5 = X4 )
                        & ? [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                            & X5 = X4 ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_tmap_1])).

cnf(c_0_35,plain,
    ( u1_struct_0(X1) = k1_setfam_1(k6_enumset1(u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X4)))
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | r1_tsep_1(X3,X4)
    | X1 != k2_tsep_1(X2,X3,X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_36,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,plain,
    ( v1_pre_topc(k2_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_39,negated_conjecture,(
    ! [X84,X85] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & m1_pre_topc(esk3_0,esk2_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk2_0)
      & ~ r1_tsep_1(esk3_0,esk4_0)
      & m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))
      & ( ~ m1_subset_1(X84,u1_struct_0(esk3_0))
        | X84 != esk5_0
        | ~ m1_subset_1(X85,u1_struct_0(esk4_0))
        | X85 != esk5_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_34])])])])])).

cnf(c_0_40,plain,
    ( u1_struct_0(k2_tsep_1(X1,X2,X3)) = k1_setfam_1(k6_enumset1(u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3)))
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_45,plain,(
    ! [X63,X64] :
      ( ~ r2_hidden(X63,X64)
      | r1_tarski(k1_setfam_1(X64),X63) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_46,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(esk4_0))) = u1_struct_0(k2_tsep_1(esk2_0,X1,esk4_0))
    | r1_tsep_1(X1,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])]),c_0_43]),c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_tsep_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_50,plain,(
    ! [X40,X41,X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58,X59] :
      ( ( ~ r2_hidden(X49,X48)
        | X49 = X40
        | X49 = X41
        | X49 = X42
        | X49 = X43
        | X49 = X44
        | X49 = X45
        | X49 = X46
        | X49 = X47
        | X48 != k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) )
      & ( X50 != X40
        | r2_hidden(X50,X48)
        | X48 != k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) )
      & ( X50 != X41
        | r2_hidden(X50,X48)
        | X48 != k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) )
      & ( X50 != X42
        | r2_hidden(X50,X48)
        | X48 != k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) )
      & ( X50 != X43
        | r2_hidden(X50,X48)
        | X48 != k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) )
      & ( X50 != X44
        | r2_hidden(X50,X48)
        | X48 != k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) )
      & ( X50 != X45
        | r2_hidden(X50,X48)
        | X48 != k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) )
      & ( X50 != X46
        | r2_hidden(X50,X48)
        | X48 != k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) )
      & ( X50 != X47
        | r2_hidden(X50,X48)
        | X48 != k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) )
      & ( esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) != X51
        | ~ r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) != X52
        | ~ r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) != X53
        | ~ r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) != X54
        | ~ r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) != X55
        | ~ r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) != X56
        | ~ r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) != X57
        | ~ r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) != X58
        | ~ r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | X59 = k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) )
      & ( r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)
        | esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) = X51
        | esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) = X52
        | esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) = X53
        | esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) = X54
        | esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) = X55
        | esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) = X56
        | esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) = X57
        | esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59) = X58
        | X59 = k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

fof(c_0_51,plain,(
    ! [X11,X12] : r1_tarski(k3_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0))) = u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_56,plain,(
    ! [X77,X78,X79] :
      ( ( ~ r1_tarski(u1_struct_0(X78),u1_struct_0(X79))
        | m1_pre_topc(X78,X79)
        | ~ m1_pre_topc(X79,X77)
        | ~ m1_pre_topc(X78,X77)
        | ~ v2_pre_topc(X77)
        | ~ l1_pre_topc(X77) )
      & ( ~ m1_pre_topc(X78,X79)
        | r1_tarski(u1_struct_0(X78),u1_struct_0(X79))
        | ~ m1_pre_topc(X79,X77)
        | ~ m1_pre_topc(X78,X77)
        | ~ v2_pre_topc(X77)
        | ~ l1_pre_topc(X77) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)),X1)
    | ~ r2_hidden(X1,k6_enumset1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

fof(c_0_60,plain,(
    ! [X67,X68,X69] :
      ( v2_struct_0(X67)
      | ~ l1_pre_topc(X67)
      | v2_struct_0(X68)
      | ~ m1_pre_topc(X68,X67)
      | ~ m1_subset_1(X69,u1_struct_0(X68))
      | m1_subset_1(X69,u1_struct_0(X67)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_61,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk2_0,X1,esk4_0),esk2_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_41]),c_0_42])]),c_0_44]),c_0_43])).

fof(c_0_64,plain,(
    ! [X65,X66] :
      ( ~ l1_pre_topc(X65)
      | ~ m1_pre_topc(X66,X65)
      | l1_pre_topc(X66) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_53])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_68,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_47]),c_0_49])).

cnf(c_0_70,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_71,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk3_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | X1 != esk5_0
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | X2 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(X1))
    | v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_41]),c_0_42])])).

cnf(c_0_76,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_41]),c_0_42])])).

cnf(c_0_77,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_69]),c_0_70]),c_0_47]),c_0_42])])).

cnf(c_0_78,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_47]),c_0_42])])).

cnf(c_0_79,negated_conjecture,
    ( ~ m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    | ~ m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_73])])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    | v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])]),c_0_44])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    | v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_77]),c_0_78])]),c_0_49])).

cnf(c_0_82,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_82]),c_0_41]),c_0_47]),c_0_42])]),c_0_44]),c_0_49]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:50:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.55  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.55  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.55  #
% 0.20/0.55  # Preprocessing time       : 0.029 s
% 0.20/0.55  # Presaturation interreduction done
% 0.20/0.55  
% 0.20/0.55  # Proof found!
% 0.20/0.55  # SZS status Theorem
% 0.20/0.55  # SZS output start CNFRefutation
% 0.20/0.55  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.55  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.55  fof(d5_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k2_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tsep_1)).
% 0.20/0.55  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.55  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.55  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.55  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.55  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.55  fof(dt_k2_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k2_tsep_1(X1,X2,X3)))&v1_pre_topc(k2_tsep_1(X1,X2,X3)))&m1_pre_topc(k2_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 0.20/0.55  fof(t17_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(m1_subset_1(X4,u1_struct_0(k2_tsep_1(X1,X2,X3)))=>(?[X5]:(m1_subset_1(X5,u1_struct_0(X2))&X5=X4)&?[X5]:(m1_subset_1(X5,u1_struct_0(X3))&X5=X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tmap_1)).
% 0.20/0.55  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.20/0.55  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 0.20/0.55  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.55  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.20/0.55  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.20/0.55  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.55  fof(c_0_16, plain, ![X61, X62]:k1_setfam_1(k2_tarski(X61,X62))=k3_xboole_0(X61,X62), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.55  fof(c_0_17, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.55  fof(c_0_18, plain, ![X70, X71, X72, X73]:((X73!=k2_tsep_1(X70,X71,X72)|u1_struct_0(X73)=k3_xboole_0(u1_struct_0(X71),u1_struct_0(X72))|(v2_struct_0(X73)|~v1_pre_topc(X73)|~m1_pre_topc(X73,X70))|r1_tsep_1(X71,X72)|(v2_struct_0(X72)|~m1_pre_topc(X72,X70))|(v2_struct_0(X71)|~m1_pre_topc(X71,X70))|(v2_struct_0(X70)|~l1_pre_topc(X70)))&(u1_struct_0(X73)!=k3_xboole_0(u1_struct_0(X71),u1_struct_0(X72))|X73=k2_tsep_1(X70,X71,X72)|(v2_struct_0(X73)|~v1_pre_topc(X73)|~m1_pre_topc(X73,X70))|r1_tsep_1(X71,X72)|(v2_struct_0(X72)|~m1_pre_topc(X72,X70))|(v2_struct_0(X71)|~m1_pre_topc(X71,X70))|(v2_struct_0(X70)|~l1_pre_topc(X70)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).
% 0.20/0.55  cnf(c_0_19, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.55  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.55  fof(c_0_21, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.55  fof(c_0_22, plain, ![X18, X19, X20, X21]:k3_enumset1(X18,X18,X19,X20,X21)=k2_enumset1(X18,X19,X20,X21), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.55  fof(c_0_23, plain, ![X22, X23, X24, X25, X26]:k4_enumset1(X22,X22,X23,X24,X25,X26)=k3_enumset1(X22,X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.55  fof(c_0_24, plain, ![X27, X28, X29, X30, X31, X32]:k5_enumset1(X27,X27,X28,X29,X30,X31,X32)=k4_enumset1(X27,X28,X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.55  fof(c_0_25, plain, ![X33, X34, X35, X36, X37, X38, X39]:k6_enumset1(X33,X33,X34,X35,X36,X37,X38,X39)=k5_enumset1(X33,X34,X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.55  cnf(c_0_26, plain, (u1_struct_0(X1)=k3_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|r1_tsep_1(X3,X4)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k2_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.55  cnf(c_0_27, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.55  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.55  cnf(c_0_29, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.55  cnf(c_0_30, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.55  cnf(c_0_31, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.55  cnf(c_0_32, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.55  fof(c_0_33, plain, ![X74, X75, X76]:(((~v2_struct_0(k2_tsep_1(X74,X75,X76))|(v2_struct_0(X74)|~l1_pre_topc(X74)|v2_struct_0(X75)|~m1_pre_topc(X75,X74)|v2_struct_0(X76)|~m1_pre_topc(X76,X74)))&(v1_pre_topc(k2_tsep_1(X74,X75,X76))|(v2_struct_0(X74)|~l1_pre_topc(X74)|v2_struct_0(X75)|~m1_pre_topc(X75,X74)|v2_struct_0(X76)|~m1_pre_topc(X76,X74))))&(m1_pre_topc(k2_tsep_1(X74,X75,X76),X74)|(v2_struct_0(X74)|~l1_pre_topc(X74)|v2_struct_0(X75)|~m1_pre_topc(X75,X74)|v2_struct_0(X76)|~m1_pre_topc(X76,X74)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).
% 0.20/0.55  fof(c_0_34, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(m1_subset_1(X4,u1_struct_0(k2_tsep_1(X1,X2,X3)))=>(?[X5]:(m1_subset_1(X5,u1_struct_0(X2))&X5=X4)&?[X5]:(m1_subset_1(X5,u1_struct_0(X3))&X5=X4)))))))), inference(assume_negation,[status(cth)],[t17_tmap_1])).
% 0.20/0.55  cnf(c_0_35, plain, (u1_struct_0(X1)=k1_setfam_1(k6_enumset1(u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X4)))|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|r1_tsep_1(X3,X4)|X1!=k2_tsep_1(X2,X3,X4)|~l1_pre_topc(X2)|~v1_pre_topc(X1)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.55  cnf(c_0_36, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.55  cnf(c_0_37, plain, (v1_pre_topc(k2_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.55  cnf(c_0_38, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k2_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.55  fof(c_0_39, negated_conjecture, ![X84, X85]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&(~r1_tsep_1(esk3_0,esk4_0)&(m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))&(~m1_subset_1(X84,u1_struct_0(esk3_0))|X84!=esk5_0|(~m1_subset_1(X85,u1_struct_0(esk4_0))|X85!=esk5_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_34])])])])])).
% 0.20/0.55  cnf(c_0_40, plain, (u1_struct_0(k2_tsep_1(X1,X2,X3))=k1_setfam_1(k6_enumset1(u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3)))|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.20/0.55  cnf(c_0_41, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.55  cnf(c_0_42, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.55  cnf(c_0_43, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.55  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.55  fof(c_0_45, plain, ![X63, X64]:(~r2_hidden(X63,X64)|r1_tarski(k1_setfam_1(X64),X63)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.20/0.55  cnf(c_0_46, negated_conjecture, (k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(esk4_0)))=u1_struct_0(k2_tsep_1(esk2_0,X1,esk4_0))|r1_tsep_1(X1,esk4_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])]), c_0_43]), c_0_44])).
% 0.20/0.55  cnf(c_0_47, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.55  cnf(c_0_48, negated_conjecture, (~r1_tsep_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.55  cnf(c_0_49, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.55  fof(c_0_50, plain, ![X40, X41, X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59]:(((~r2_hidden(X49,X48)|(X49=X40|X49=X41|X49=X42|X49=X43|X49=X44|X49=X45|X49=X46|X49=X47)|X48!=k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47))&((((((((X50!=X40|r2_hidden(X50,X48)|X48!=k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47))&(X50!=X41|r2_hidden(X50,X48)|X48!=k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47)))&(X50!=X42|r2_hidden(X50,X48)|X48!=k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47)))&(X50!=X43|r2_hidden(X50,X48)|X48!=k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47)))&(X50!=X44|r2_hidden(X50,X48)|X48!=k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47)))&(X50!=X45|r2_hidden(X50,X48)|X48!=k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47)))&(X50!=X46|r2_hidden(X50,X48)|X48!=k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47)))&(X50!=X47|r2_hidden(X50,X48)|X48!=k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47))))&(((((((((esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)!=X51|~r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58))&(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)!=X52|~r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)!=X53|~r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)!=X54|~r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)!=X55|~r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)!=X56|~r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)!=X57|~r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)!=X58|~r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)|X59=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))&(r2_hidden(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59),X59)|(esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)=X51|esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)=X52|esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)=X53|esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)=X54|esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)=X55|esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)=X56|esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)=X57|esk1_9(X51,X52,X53,X54,X55,X56,X57,X58,X59)=X58)|X59=k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.20/0.55  fof(c_0_51, plain, ![X11, X12]:r1_tarski(k3_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.55  cnf(c_0_52, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.55  cnf(c_0_53, negated_conjecture, (k1_setfam_1(k6_enumset1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0)))=u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49])).
% 0.20/0.55  cnf(c_0_54, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X5,X6,X7,X8,X9,X10,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.55  cnf(c_0_55, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.55  fof(c_0_56, plain, ![X77, X78, X79]:((~r1_tarski(u1_struct_0(X78),u1_struct_0(X79))|m1_pre_topc(X78,X79)|~m1_pre_topc(X79,X77)|~m1_pre_topc(X78,X77)|(~v2_pre_topc(X77)|~l1_pre_topc(X77)))&(~m1_pre_topc(X78,X79)|r1_tarski(u1_struct_0(X78),u1_struct_0(X79))|~m1_pre_topc(X79,X77)|~m1_pre_topc(X78,X77)|(~v2_pre_topc(X77)|~l1_pre_topc(X77)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.20/0.55  cnf(c_0_57, negated_conjecture, (r1_tarski(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)),X1)|~r2_hidden(X1,k6_enumset1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.55  cnf(c_0_58, plain, (r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).
% 0.20/0.55  cnf(c_0_59, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.55  fof(c_0_60, plain, ![X67, X68, X69]:(v2_struct_0(X67)|~l1_pre_topc(X67)|(v2_struct_0(X68)|~m1_pre_topc(X68,X67)|(~m1_subset_1(X69,u1_struct_0(X68))|m1_subset_1(X69,u1_struct_0(X67))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.20/0.55  cnf(c_0_61, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.55  cnf(c_0_62, negated_conjecture, (r1_tarski(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.55  cnf(c_0_63, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk2_0,X1,esk4_0),esk2_0)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_41]), c_0_42])]), c_0_44]), c_0_43])).
% 0.20/0.55  fof(c_0_64, plain, ![X65, X66]:(~l1_pre_topc(X65)|(~m1_pre_topc(X66,X65)|l1_pre_topc(X66))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.55  cnf(c_0_65, negated_conjecture, (r1_tarski(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_59, c_0_53])).
% 0.20/0.55  cnf(c_0_66, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.55  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.55  cnf(c_0_68, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk4_0)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.55  cnf(c_0_69, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_47]), c_0_49])).
% 0.20/0.55  cnf(c_0_70, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.55  cnf(c_0_71, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.55  cnf(c_0_72, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk3_0)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_61, c_0_65])).
% 0.20/0.55  cnf(c_0_73, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk3_0))|X1!=esk5_0|~m1_subset_1(X2,u1_struct_0(esk4_0))|X2!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.55  cnf(c_0_74, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(X1))|v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))|v2_struct_0(X1)|~m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.55  cnf(c_0_75, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_41]), c_0_42])])).
% 0.20/0.55  cnf(c_0_76, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_41]), c_0_42])])).
% 0.20/0.55  cnf(c_0_77, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_69]), c_0_70]), c_0_47]), c_0_42])])).
% 0.20/0.55  cnf(c_0_78, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_47]), c_0_42])])).
% 0.20/0.55  cnf(c_0_79, negated_conjecture, (~m1_subset_1(esk5_0,u1_struct_0(esk4_0))|~m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_73])])).
% 0.20/0.55  cnf(c_0_80, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))|v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])]), c_0_44])).
% 0.20/0.55  cnf(c_0_81, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))|v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_77]), c_0_78])]), c_0_49])).
% 0.20/0.55  cnf(c_0_82, negated_conjecture, (v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.20/0.55  cnf(c_0_83, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_82]), c_0_41]), c_0_47]), c_0_42])]), c_0_44]), c_0_49]), c_0_43]), ['proof']).
% 0.20/0.55  # SZS output end CNFRefutation
% 0.20/0.55  # Proof object total steps             : 84
% 0.20/0.55  # Proof object clause steps            : 51
% 0.20/0.55  # Proof object formula steps           : 33
% 0.20/0.55  # Proof object conjectures             : 32
% 0.20/0.55  # Proof object clause conjectures      : 29
% 0.20/0.55  # Proof object formula conjectures     : 3
% 0.20/0.55  # Proof object initial clauses used    : 27
% 0.20/0.55  # Proof object initial formulas used   : 16
% 0.20/0.55  # Proof object generating inferences   : 18
% 0.20/0.55  # Proof object simplifying inferences  : 58
% 0.20/0.55  # Training examples: 0 positive, 0 negative
% 0.20/0.55  # Parsed axioms                        : 16
% 0.20/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.55  # Initial clauses                      : 46
% 0.20/0.55  # Removed in clause preprocessing      : 7
% 0.20/0.55  # Initial clauses in saturation        : 39
% 0.20/0.55  # Processed clauses                    : 541
% 0.20/0.55  # ...of these trivial                  : 0
% 0.20/0.55  # ...subsumed                          : 11
% 0.20/0.55  # ...remaining for further processing  : 530
% 0.20/0.55  # Other redundant clauses eliminated   : 622
% 0.20/0.55  # Clauses deleted for lack of memory   : 0
% 0.20/0.55  # Backward-subsumed                    : 2
% 0.20/0.55  # Backward-rewritten                   : 116
% 0.20/0.55  # Generated clauses                    : 7501
% 0.20/0.55  # ...of the previous two non-trivial   : 5670
% 0.20/0.55  # Contextual simplify-reflections      : 4
% 0.20/0.55  # Paramodulations                      : 4468
% 0.20/0.55  # Factorizations                       : 2420
% 0.20/0.55  # Equation resolutions                 : 622
% 0.20/0.55  # Propositional unsat checks           : 0
% 0.20/0.55  #    Propositional check models        : 0
% 0.20/0.55  #    Propositional check unsatisfiable : 0
% 0.20/0.55  #    Propositional clauses             : 0
% 0.20/0.55  #    Propositional clauses after purity: 0
% 0.20/0.55  #    Propositional unsat core size     : 0
% 0.20/0.55  #    Propositional preprocessing time  : 0.000
% 0.20/0.55  #    Propositional encoding time       : 0.000
% 0.20/0.55  #    Propositional solver time         : 0.000
% 0.20/0.55  #    Success case prop preproc time    : 0.000
% 0.20/0.55  #    Success case prop encoding time   : 0.000
% 0.20/0.55  #    Success case prop solver time     : 0.000
% 0.20/0.55  # Current number of processed clauses  : 362
% 0.20/0.55  #    Positive orientable unit clauses  : 34
% 0.20/0.55  #    Positive unorientable unit clauses: 0
% 0.20/0.55  #    Negative unit clauses             : 4
% 0.20/0.55  #    Non-unit-clauses                  : 324
% 0.20/0.55  # Current number of unprocessed clauses: 5207
% 0.20/0.55  # ...number of literals in the above   : 29309
% 0.20/0.55  # Current number of archived formulas  : 0
% 0.20/0.55  # Current number of archived clauses   : 164
% 0.20/0.55  # Clause-clause subsumption calls (NU) : 145750
% 0.20/0.55  # Rec. Clause-clause subsumption calls : 48645
% 0.20/0.55  # Non-unit clause-clause subsumptions  : 15
% 0.20/0.55  # Unit Clause-clause subsumption calls : 1350
% 0.20/0.55  # Rewrite failures with RHS unbound    : 0
% 0.20/0.55  # BW rewrite match attempts            : 73
% 0.20/0.55  # BW rewrite match successes           : 3
% 0.20/0.55  # Condensation attempts                : 0
% 0.20/0.55  # Condensation successes               : 0
% 0.20/0.55  # Termbank termtop insertions          : 217574
% 0.20/0.55  
% 0.20/0.55  # -------------------------------------------------
% 0.20/0.55  # User time                : 0.193 s
% 0.20/0.55  # System time              : 0.012 s
% 0.20/0.55  # Total time               : 0.205 s
% 0.20/0.55  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
