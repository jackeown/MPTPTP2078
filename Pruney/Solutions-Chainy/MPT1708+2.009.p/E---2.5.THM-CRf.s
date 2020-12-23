%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:53 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 335 expanded)
%              Number of clauses        :   50 ( 118 expanded)
%              Number of leaves         :   15 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :  364 (2648 expanded)
%              Number of equality atoms :   94 ( 421 expanded)
%              Maximal formula depth    :   42 (   5 average)
%              Maximal clause size      :   60 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tmap_1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(d5_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( X8 = k5_enumset1(X1,X2,X3,X4,X5,X6,X7)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X9 != X1
              & X9 != X2
              & X9 != X3
              & X9 != X4
              & X9 != X5
              & X9 != X6
              & X9 != X7 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_enumset1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(c_0_15,plain,(
    ! [X51,X52] : k1_setfam_1(k2_tarski(X51,X52)) = k3_xboole_0(X51,X52) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_16,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X60,X61,X62,X63] :
      ( ( X63 != k2_tsep_1(X60,X61,X62)
        | u1_struct_0(X63) = k3_xboole_0(u1_struct_0(X61),u1_struct_0(X62))
        | v2_struct_0(X63)
        | ~ v1_pre_topc(X63)
        | ~ m1_pre_topc(X63,X60)
        | r1_tsep_1(X61,X62)
        | v2_struct_0(X62)
        | ~ m1_pre_topc(X62,X60)
        | v2_struct_0(X61)
        | ~ m1_pre_topc(X61,X60)
        | v2_struct_0(X60)
        | ~ l1_pre_topc(X60) )
      & ( u1_struct_0(X63) != k3_xboole_0(u1_struct_0(X61),u1_struct_0(X62))
        | X63 = k2_tsep_1(X60,X61,X62)
        | v2_struct_0(X63)
        | ~ v1_pre_topc(X63)
        | ~ m1_pre_topc(X63,X60)
        | r1_tsep_1(X61,X62)
        | v2_struct_0(X62)
        | ~ m1_pre_topc(X62,X60)
        | v2_struct_0(X61)
        | ~ m1_pre_topc(X61,X60)
        | v2_struct_0(X60)
        | ~ l1_pre_topc(X60) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_21,plain,(
    ! [X17,X18,X19,X20] : k3_enumset1(X17,X17,X18,X19,X20) = k2_enumset1(X17,X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_22,plain,(
    ! [X21,X22,X23,X24,X25] : k4_enumset1(X21,X21,X22,X23,X24,X25) = k3_enumset1(X21,X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_23,plain,(
    ! [X26,X27,X28,X29,X30,X31] : k5_enumset1(X26,X26,X27,X28,X29,X30,X31) = k4_enumset1(X26,X27,X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

cnf(c_0_24,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X64,X65,X66] :
      ( ( ~ v2_struct_0(k2_tsep_1(X64,X65,X66))
        | v2_struct_0(X64)
        | ~ l1_pre_topc(X64)
        | v2_struct_0(X65)
        | ~ m1_pre_topc(X65,X64)
        | v2_struct_0(X66)
        | ~ m1_pre_topc(X66,X64) )
      & ( v1_pre_topc(k2_tsep_1(X64,X65,X66))
        | v2_struct_0(X64)
        | ~ l1_pre_topc(X64)
        | v2_struct_0(X65)
        | ~ m1_pre_topc(X65,X64)
        | v2_struct_0(X66)
        | ~ m1_pre_topc(X66,X64) )
      & ( m1_pre_topc(k2_tsep_1(X64,X65,X66),X64)
        | v2_struct_0(X64)
        | ~ l1_pre_topc(X64)
        | v2_struct_0(X65)
        | ~ m1_pre_topc(X65,X64)
        | v2_struct_0(X66)
        | ~ m1_pre_topc(X66,X64) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

fof(c_0_31,negated_conjecture,(
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

cnf(c_0_32,plain,
    ( u1_struct_0(X1) = k1_setfam_1(k5_enumset1(u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X4)))
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
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_33,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,plain,
    ( v1_pre_topc(k2_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,negated_conjecture,(
    ! [X74,X75] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & m1_pre_topc(esk3_0,esk2_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk2_0)
      & ~ r1_tsep_1(esk3_0,esk4_0)
      & m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))
      & ( ~ m1_subset_1(X74,u1_struct_0(esk3_0))
        | X74 != esk5_0
        | ~ m1_subset_1(X75,u1_struct_0(esk4_0))
        | X75 != esk5_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])])).

cnf(c_0_37,plain,
    ( u1_struct_0(k2_tsep_1(X1,X2,X3)) = k1_setfam_1(k5_enumset1(u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3)))
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_42,plain,(
    ! [X53,X54] :
      ( ~ r2_hidden(X53,X54)
      | r1_tarski(k1_setfam_1(X54),X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_43,negated_conjecture,
    ( k1_setfam_1(k5_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(esk4_0))) = u1_struct_0(k2_tsep_1(esk2_0,X1,esk4_0))
    | r1_tsep_1(X1,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])]),c_0_40]),c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tsep_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_47,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38,X39,X40,X41,X42,X43,X44,X45,X46,X47,X48,X49] :
      ( ( ~ r2_hidden(X40,X39)
        | X40 = X32
        | X40 = X33
        | X40 = X34
        | X40 = X35
        | X40 = X36
        | X40 = X37
        | X40 = X38
        | X39 != k5_enumset1(X32,X33,X34,X35,X36,X37,X38) )
      & ( X41 != X32
        | r2_hidden(X41,X39)
        | X39 != k5_enumset1(X32,X33,X34,X35,X36,X37,X38) )
      & ( X41 != X33
        | r2_hidden(X41,X39)
        | X39 != k5_enumset1(X32,X33,X34,X35,X36,X37,X38) )
      & ( X41 != X34
        | r2_hidden(X41,X39)
        | X39 != k5_enumset1(X32,X33,X34,X35,X36,X37,X38) )
      & ( X41 != X35
        | r2_hidden(X41,X39)
        | X39 != k5_enumset1(X32,X33,X34,X35,X36,X37,X38) )
      & ( X41 != X36
        | r2_hidden(X41,X39)
        | X39 != k5_enumset1(X32,X33,X34,X35,X36,X37,X38) )
      & ( X41 != X37
        | r2_hidden(X41,X39)
        | X39 != k5_enumset1(X32,X33,X34,X35,X36,X37,X38) )
      & ( X41 != X38
        | r2_hidden(X41,X39)
        | X39 != k5_enumset1(X32,X33,X34,X35,X36,X37,X38) )
      & ( esk1_8(X42,X43,X44,X45,X46,X47,X48,X49) != X42
        | ~ r2_hidden(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49),X49)
        | X49 = k5_enumset1(X42,X43,X44,X45,X46,X47,X48) )
      & ( esk1_8(X42,X43,X44,X45,X46,X47,X48,X49) != X43
        | ~ r2_hidden(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49),X49)
        | X49 = k5_enumset1(X42,X43,X44,X45,X46,X47,X48) )
      & ( esk1_8(X42,X43,X44,X45,X46,X47,X48,X49) != X44
        | ~ r2_hidden(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49),X49)
        | X49 = k5_enumset1(X42,X43,X44,X45,X46,X47,X48) )
      & ( esk1_8(X42,X43,X44,X45,X46,X47,X48,X49) != X45
        | ~ r2_hidden(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49),X49)
        | X49 = k5_enumset1(X42,X43,X44,X45,X46,X47,X48) )
      & ( esk1_8(X42,X43,X44,X45,X46,X47,X48,X49) != X46
        | ~ r2_hidden(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49),X49)
        | X49 = k5_enumset1(X42,X43,X44,X45,X46,X47,X48) )
      & ( esk1_8(X42,X43,X44,X45,X46,X47,X48,X49) != X47
        | ~ r2_hidden(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49),X49)
        | X49 = k5_enumset1(X42,X43,X44,X45,X46,X47,X48) )
      & ( esk1_8(X42,X43,X44,X45,X46,X47,X48,X49) != X48
        | ~ r2_hidden(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49),X49)
        | X49 = k5_enumset1(X42,X43,X44,X45,X46,X47,X48) )
      & ( r2_hidden(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49),X49)
        | esk1_8(X42,X43,X44,X45,X46,X47,X48,X49) = X42
        | esk1_8(X42,X43,X44,X45,X46,X47,X48,X49) = X43
        | esk1_8(X42,X43,X44,X45,X46,X47,X48,X49) = X44
        | esk1_8(X42,X43,X44,X45,X46,X47,X48,X49) = X45
        | esk1_8(X42,X43,X44,X45,X46,X47,X48,X49) = X46
        | esk1_8(X42,X43,X44,X45,X46,X47,X48,X49) = X47
        | esk1_8(X42,X43,X44,X45,X46,X47,X48,X49) = X48
        | X49 = k5_enumset1(X42,X43,X44,X45,X46,X47,X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_enumset1])])])])])])).

fof(c_0_48,plain,(
    ! [X10,X11] : r1_tarski(k3_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k1_setfam_1(k5_enumset1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0))) = u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X5,X6,X7,X8,X9,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_53,plain,(
    ! [X67,X68,X69] :
      ( ( ~ r1_tarski(u1_struct_0(X68),u1_struct_0(X69))
        | m1_pre_topc(X68,X69)
        | ~ m1_pre_topc(X69,X67)
        | ~ m1_pre_topc(X68,X67)
        | ~ v2_pre_topc(X67)
        | ~ l1_pre_topc(X67) )
      & ( ~ m1_pre_topc(X68,X69)
        | r1_tarski(u1_struct_0(X68),u1_struct_0(X69))
        | ~ m1_pre_topc(X69,X67)
        | ~ m1_pre_topc(X68,X67)
        | ~ v2_pre_topc(X67)
        | ~ l1_pre_topc(X67) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)),X1)
    | ~ r2_hidden(X1,k5_enumset1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X3,X4,X5,X6,X7,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_51])])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

fof(c_0_57,plain,(
    ! [X57,X58,X59] :
      ( v2_struct_0(X57)
      | ~ l1_pre_topc(X57)
      | v2_struct_0(X58)
      | ~ m1_pre_topc(X58,X57)
      | ~ m1_subset_1(X59,u1_struct_0(X58))
      | m1_subset_1(X59,u1_struct_0(X57)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_58,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk2_0,X1,esk4_0),esk2_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_38]),c_0_39])]),c_0_41]),c_0_40])).

fof(c_0_61,plain,(
    ! [X55,X56] :
      ( ~ l1_pre_topc(X55)
      | ~ m1_pre_topc(X56,X55)
      | l1_pre_topc(X56) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_50])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_65,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_44]),c_0_46])).

cnf(c_0_67,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_68,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk3_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | X1 != esk5_0
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | X2 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(X1))
    | v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_38]),c_0_39])])).

cnf(c_0_73,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_38]),c_0_39])])).

cnf(c_0_74,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_66]),c_0_67]),c_0_44]),c_0_39])])).

cnf(c_0_75,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_44]),c_0_39])])).

cnf(c_0_76,negated_conjecture,
    ( ~ m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    | ~ m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_70])])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    | v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])]),c_0_41])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    | v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_74]),c_0_75])]),c_0_46])).

cnf(c_0_79,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_79]),c_0_38]),c_0_44]),c_0_39])]),c_0_41]),c_0_46]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.47  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.029 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.47  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.47  fof(d5_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k2_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tsep_1)).
% 0.19/0.47  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.47  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.47  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.47  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.47  fof(dt_k2_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k2_tsep_1(X1,X2,X3)))&v1_pre_topc(k2_tsep_1(X1,X2,X3)))&m1_pre_topc(k2_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 0.19/0.47  fof(t17_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(m1_subset_1(X4,u1_struct_0(k2_tsep_1(X1,X2,X3)))=>(?[X5]:(m1_subset_1(X5,u1_struct_0(X2))&X5=X4)&?[X5]:(m1_subset_1(X5,u1_struct_0(X3))&X5=X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tmap_1)).
% 0.19/0.47  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.19/0.47  fof(d5_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:(X8=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)<=>![X9]:(r2_hidden(X9,X8)<=>~(((((((X9!=X1&X9!=X2)&X9!=X3)&X9!=X4)&X9!=X5)&X9!=X6)&X9!=X7)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_enumset1)).
% 0.19/0.47  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.47  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.19/0.47  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.19/0.47  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.47  fof(c_0_15, plain, ![X51, X52]:k1_setfam_1(k2_tarski(X51,X52))=k3_xboole_0(X51,X52), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.47  fof(c_0_16, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.47  fof(c_0_17, plain, ![X60, X61, X62, X63]:((X63!=k2_tsep_1(X60,X61,X62)|u1_struct_0(X63)=k3_xboole_0(u1_struct_0(X61),u1_struct_0(X62))|(v2_struct_0(X63)|~v1_pre_topc(X63)|~m1_pre_topc(X63,X60))|r1_tsep_1(X61,X62)|(v2_struct_0(X62)|~m1_pre_topc(X62,X60))|(v2_struct_0(X61)|~m1_pre_topc(X61,X60))|(v2_struct_0(X60)|~l1_pre_topc(X60)))&(u1_struct_0(X63)!=k3_xboole_0(u1_struct_0(X61),u1_struct_0(X62))|X63=k2_tsep_1(X60,X61,X62)|(v2_struct_0(X63)|~v1_pre_topc(X63)|~m1_pre_topc(X63,X60))|r1_tsep_1(X61,X62)|(v2_struct_0(X62)|~m1_pre_topc(X62,X60))|(v2_struct_0(X61)|~m1_pre_topc(X61,X60))|(v2_struct_0(X60)|~l1_pre_topc(X60)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).
% 0.19/0.47  cnf(c_0_18, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.47  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.47  fof(c_0_20, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.47  fof(c_0_21, plain, ![X17, X18, X19, X20]:k3_enumset1(X17,X17,X18,X19,X20)=k2_enumset1(X17,X18,X19,X20), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.47  fof(c_0_22, plain, ![X21, X22, X23, X24, X25]:k4_enumset1(X21,X21,X22,X23,X24,X25)=k3_enumset1(X21,X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.47  fof(c_0_23, plain, ![X26, X27, X28, X29, X30, X31]:k5_enumset1(X26,X26,X27,X28,X29,X30,X31)=k4_enumset1(X26,X27,X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.47  cnf(c_0_24, plain, (u1_struct_0(X1)=k3_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|r1_tsep_1(X3,X4)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k2_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.47  cnf(c_0_25, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.47  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.47  cnf(c_0_27, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.47  cnf(c_0_28, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_29, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.47  fof(c_0_30, plain, ![X64, X65, X66]:(((~v2_struct_0(k2_tsep_1(X64,X65,X66))|(v2_struct_0(X64)|~l1_pre_topc(X64)|v2_struct_0(X65)|~m1_pre_topc(X65,X64)|v2_struct_0(X66)|~m1_pre_topc(X66,X64)))&(v1_pre_topc(k2_tsep_1(X64,X65,X66))|(v2_struct_0(X64)|~l1_pre_topc(X64)|v2_struct_0(X65)|~m1_pre_topc(X65,X64)|v2_struct_0(X66)|~m1_pre_topc(X66,X64))))&(m1_pre_topc(k2_tsep_1(X64,X65,X66),X64)|(v2_struct_0(X64)|~l1_pre_topc(X64)|v2_struct_0(X65)|~m1_pre_topc(X65,X64)|v2_struct_0(X66)|~m1_pre_topc(X66,X64)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).
% 0.19/0.47  fof(c_0_31, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(m1_subset_1(X4,u1_struct_0(k2_tsep_1(X1,X2,X3)))=>(?[X5]:(m1_subset_1(X5,u1_struct_0(X2))&X5=X4)&?[X5]:(m1_subset_1(X5,u1_struct_0(X3))&X5=X4)))))))), inference(assume_negation,[status(cth)],[t17_tmap_1])).
% 0.19/0.47  cnf(c_0_32, plain, (u1_struct_0(X1)=k1_setfam_1(k5_enumset1(u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X4)))|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|r1_tsep_1(X3,X4)|X1!=k2_tsep_1(X2,X3,X4)|~l1_pre_topc(X2)|~v1_pre_topc(X1)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.19/0.47  cnf(c_0_33, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.47  cnf(c_0_34, plain, (v1_pre_topc(k2_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.47  cnf(c_0_35, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k2_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.47  fof(c_0_36, negated_conjecture, ![X74, X75]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&(~r1_tsep_1(esk3_0,esk4_0)&(m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))&(~m1_subset_1(X74,u1_struct_0(esk3_0))|X74!=esk5_0|(~m1_subset_1(X75,u1_struct_0(esk4_0))|X75!=esk5_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])])).
% 0.19/0.47  cnf(c_0_37, plain, (u1_struct_0(k2_tsep_1(X1,X2,X3))=k1_setfam_1(k5_enumset1(u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3)))|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.19/0.47  cnf(c_0_38, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.47  cnf(c_0_39, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.47  cnf(c_0_40, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.47  cnf(c_0_41, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.47  fof(c_0_42, plain, ![X53, X54]:(~r2_hidden(X53,X54)|r1_tarski(k1_setfam_1(X54),X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.19/0.47  cnf(c_0_43, negated_conjecture, (k1_setfam_1(k5_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(esk4_0)))=u1_struct_0(k2_tsep_1(esk2_0,X1,esk4_0))|r1_tsep_1(X1,esk4_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])]), c_0_40]), c_0_41])).
% 0.19/0.47  cnf(c_0_44, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.47  cnf(c_0_45, negated_conjecture, (~r1_tsep_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.47  cnf(c_0_46, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.47  fof(c_0_47, plain, ![X32, X33, X34, X35, X36, X37, X38, X39, X40, X41, X42, X43, X44, X45, X46, X47, X48, X49]:(((~r2_hidden(X40,X39)|(X40=X32|X40=X33|X40=X34|X40=X35|X40=X36|X40=X37|X40=X38)|X39!=k5_enumset1(X32,X33,X34,X35,X36,X37,X38))&(((((((X41!=X32|r2_hidden(X41,X39)|X39!=k5_enumset1(X32,X33,X34,X35,X36,X37,X38))&(X41!=X33|r2_hidden(X41,X39)|X39!=k5_enumset1(X32,X33,X34,X35,X36,X37,X38)))&(X41!=X34|r2_hidden(X41,X39)|X39!=k5_enumset1(X32,X33,X34,X35,X36,X37,X38)))&(X41!=X35|r2_hidden(X41,X39)|X39!=k5_enumset1(X32,X33,X34,X35,X36,X37,X38)))&(X41!=X36|r2_hidden(X41,X39)|X39!=k5_enumset1(X32,X33,X34,X35,X36,X37,X38)))&(X41!=X37|r2_hidden(X41,X39)|X39!=k5_enumset1(X32,X33,X34,X35,X36,X37,X38)))&(X41!=X38|r2_hidden(X41,X39)|X39!=k5_enumset1(X32,X33,X34,X35,X36,X37,X38))))&((((((((esk1_8(X42,X43,X44,X45,X46,X47,X48,X49)!=X42|~r2_hidden(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49),X49)|X49=k5_enumset1(X42,X43,X44,X45,X46,X47,X48))&(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49)!=X43|~r2_hidden(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49),X49)|X49=k5_enumset1(X42,X43,X44,X45,X46,X47,X48)))&(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49)!=X44|~r2_hidden(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49),X49)|X49=k5_enumset1(X42,X43,X44,X45,X46,X47,X48)))&(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49)!=X45|~r2_hidden(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49),X49)|X49=k5_enumset1(X42,X43,X44,X45,X46,X47,X48)))&(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49)!=X46|~r2_hidden(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49),X49)|X49=k5_enumset1(X42,X43,X44,X45,X46,X47,X48)))&(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49)!=X47|~r2_hidden(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49),X49)|X49=k5_enumset1(X42,X43,X44,X45,X46,X47,X48)))&(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49)!=X48|~r2_hidden(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49),X49)|X49=k5_enumset1(X42,X43,X44,X45,X46,X47,X48)))&(r2_hidden(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49),X49)|(esk1_8(X42,X43,X44,X45,X46,X47,X48,X49)=X42|esk1_8(X42,X43,X44,X45,X46,X47,X48,X49)=X43|esk1_8(X42,X43,X44,X45,X46,X47,X48,X49)=X44|esk1_8(X42,X43,X44,X45,X46,X47,X48,X49)=X45|esk1_8(X42,X43,X44,X45,X46,X47,X48,X49)=X46|esk1_8(X42,X43,X44,X45,X46,X47,X48,X49)=X47|esk1_8(X42,X43,X44,X45,X46,X47,X48,X49)=X48)|X49=k5_enumset1(X42,X43,X44,X45,X46,X47,X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_enumset1])])])])])])).
% 0.19/0.47  fof(c_0_48, plain, ![X10, X11]:r1_tarski(k3_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.47  cnf(c_0_49, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.47  cnf(c_0_50, negated_conjecture, (k1_setfam_1(k5_enumset1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0)))=u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])).
% 0.19/0.47  cnf(c_0_51, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X5,X6,X7,X8,X9,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.47  cnf(c_0_52, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.47  fof(c_0_53, plain, ![X67, X68, X69]:((~r1_tarski(u1_struct_0(X68),u1_struct_0(X69))|m1_pre_topc(X68,X69)|~m1_pre_topc(X69,X67)|~m1_pre_topc(X68,X67)|(~v2_pre_topc(X67)|~l1_pre_topc(X67)))&(~m1_pre_topc(X68,X69)|r1_tarski(u1_struct_0(X68),u1_struct_0(X69))|~m1_pre_topc(X69,X67)|~m1_pre_topc(X68,X67)|(~v2_pre_topc(X67)|~l1_pre_topc(X67)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.19/0.47  cnf(c_0_54, negated_conjecture, (r1_tarski(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)),X1)|~r2_hidden(X1,k5_enumset1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.47  cnf(c_0_55, plain, (r2_hidden(X1,k5_enumset1(X2,X3,X4,X5,X6,X7,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_51])])).
% 0.19/0.47  cnf(c_0_56, plain, (r1_tarski(k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.19/0.47  fof(c_0_57, plain, ![X57, X58, X59]:(v2_struct_0(X57)|~l1_pre_topc(X57)|(v2_struct_0(X58)|~m1_pre_topc(X58,X57)|(~m1_subset_1(X59,u1_struct_0(X58))|m1_subset_1(X59,u1_struct_0(X57))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.19/0.47  cnf(c_0_58, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.47  cnf(c_0_59, negated_conjecture, (r1_tarski(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.47  cnf(c_0_60, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk2_0,X1,esk4_0),esk2_0)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_38]), c_0_39])]), c_0_41]), c_0_40])).
% 0.19/0.47  fof(c_0_61, plain, ![X55, X56]:(~l1_pre_topc(X55)|(~m1_pre_topc(X56,X55)|l1_pre_topc(X56))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.47  cnf(c_0_62, negated_conjecture, (r1_tarski(u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_56, c_0_50])).
% 0.19/0.47  cnf(c_0_63, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.47  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.47  cnf(c_0_65, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk4_0)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.47  cnf(c_0_66, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_44]), c_0_46])).
% 0.19/0.47  cnf(c_0_67, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.47  cnf(c_0_68, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.47  cnf(c_0_69, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk3_0)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_58, c_0_62])).
% 0.19/0.47  cnf(c_0_70, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk3_0))|X1!=esk5_0|~m1_subset_1(X2,u1_struct_0(esk4_0))|X2!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.47  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(X1))|v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))|v2_struct_0(X1)|~m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.47  cnf(c_0_72, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_38]), c_0_39])])).
% 0.19/0.47  cnf(c_0_73, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_38]), c_0_39])])).
% 0.19/0.47  cnf(c_0_74, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk2_0,esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_66]), c_0_67]), c_0_44]), c_0_39])])).
% 0.19/0.47  cnf(c_0_75, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_44]), c_0_39])])).
% 0.19/0.47  cnf(c_0_76, negated_conjecture, (~m1_subset_1(esk5_0,u1_struct_0(esk4_0))|~m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_70])])).
% 0.19/0.47  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))|v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])]), c_0_41])).
% 0.19/0.47  cnf(c_0_78, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))|v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_74]), c_0_75])]), c_0_46])).
% 0.19/0.47  cnf(c_0_79, negated_conjecture, (v2_struct_0(k2_tsep_1(esk2_0,esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])).
% 0.19/0.47  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_79]), c_0_38]), c_0_44]), c_0_39])]), c_0_41]), c_0_46]), c_0_40]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 81
% 0.19/0.47  # Proof object clause steps            : 50
% 0.19/0.47  # Proof object formula steps           : 31
% 0.19/0.47  # Proof object conjectures             : 32
% 0.19/0.47  # Proof object clause conjectures      : 29
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 26
% 0.19/0.47  # Proof object initial formulas used   : 15
% 0.19/0.47  # Proof object generating inferences   : 18
% 0.19/0.47  # Proof object simplifying inferences  : 56
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 15
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 43
% 0.19/0.47  # Removed in clause preprocessing      : 6
% 0.19/0.47  # Initial clauses in saturation        : 37
% 0.19/0.47  # Processed clauses                    : 429
% 0.19/0.47  # ...of these trivial                  : 0
% 0.19/0.47  # ...subsumed                          : 9
% 0.19/0.47  # ...remaining for further processing  : 420
% 0.19/0.47  # Other redundant clauses eliminated   : 180
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 2
% 0.19/0.47  # Backward-rewritten                   : 90
% 0.19/0.47  # Generated clauses                    : 3738
% 0.19/0.47  # ...of the previous two non-trivial   : 3229
% 0.19/0.47  # Contextual simplify-reflections      : 4
% 0.19/0.47  # Paramodulations                      : 2906
% 0.19/0.47  # Factorizations                       : 660
% 0.19/0.47  # Equation resolutions                 : 180
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 281
% 0.19/0.47  #    Positive orientable unit clauses  : 33
% 0.19/0.47  #    Positive unorientable unit clauses: 0
% 0.19/0.47  #    Negative unit clauses             : 4
% 0.19/0.47  #    Non-unit-clauses                  : 244
% 0.19/0.47  # Current number of unprocessed clauses: 2874
% 0.19/0.47  # ...number of literals in the above   : 14830
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 135
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 113054
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 38175
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 13
% 0.19/0.47  # Unit Clause-clause subsumption calls : 1098
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 59
% 0.19/0.47  # BW rewrite match successes           : 3
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 131736
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.121 s
% 0.19/0.47  # System time              : 0.013 s
% 0.19/0.47  # Total time               : 0.134 s
% 0.19/0.47  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
