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
% DateTime   : Thu Dec  3 11:17:01 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 447 expanded)
%              Number of clauses        :   53 ( 187 expanded)
%              Number of leaves         :    9 ( 105 expanded)
%              Depth                    :   23
%              Number of atoms          :  291 (2995 expanded)
%              Number of equality atoms :    5 (  20 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_tmap_1,conjecture,(
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
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( m1_pre_topc(X2,X3)
                   => ( ( ~ r1_tsep_1(X3,X4)
                        & ~ r1_tsep_1(X4,X3) )
                      | ( r1_tsep_1(X2,X4)
                        & r1_tsep_1(X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tmap_1)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t64_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4)
        & r1_xboole_0(X2,X4) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

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

fof(c_0_9,negated_conjecture,(
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
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ( m1_pre_topc(X2,X3)
                     => ( ( ~ r1_tsep_1(X3,X4)
                          & ~ r1_tsep_1(X4,X3) )
                        | ( r1_tsep_1(X2,X4)
                          & r1_tsep_1(X4,X2) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t24_tmap_1])).

fof(c_0_10,plain,(
    ! [X18,X19] :
      ( ~ l1_struct_0(X18)
      | ~ l1_struct_0(X19)
      | ~ r1_tsep_1(X18,X19)
      | r1_tsep_1(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & m1_pre_topc(esk2_0,esk3_0)
    & ( r1_tsep_1(esk3_0,esk4_0)
      | r1_tsep_1(esk4_0,esk3_0) )
    & ( ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk4_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

cnf(c_0_12,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X13] :
      ( ~ l1_pre_topc(X13)
      | l1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_15,plain,(
    ! [X7,X8,X9,X10] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X9,X10)
      | ~ r1_xboole_0(X8,X10)
      | r1_xboole_0(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_xboole_1])])).

fof(c_0_16,plain,(
    ! [X16,X17] :
      ( ( ~ r1_tsep_1(X16,X17)
        | r1_xboole_0(u1_struct_0(X16),u1_struct_0(X17))
        | ~ l1_struct_0(X17)
        | ~ l1_struct_0(X16) )
      & ( ~ r1_xboole_0(u1_struct_0(X16),u1_struct_0(X17))
        | r1_tsep_1(X16,X17)
        | ~ l1_struct_0(X17)
        | ~ l1_struct_0(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

fof(c_0_17,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_18,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X14,X15] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,X14)
      | l1_pre_topc(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4)
    | ~ r1_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X11,X12] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(X12,X11)
      | v2_pre_topc(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_25,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tsep_1(X3,X4)
    | ~ l1_struct_0(X4)
    | ~ l1_struct_0(X3)
    | ~ r1_tarski(X2,u1_struct_0(X4))
    | ~ r1_tarski(X1,u1_struct_0(X3)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X20,X21,X22] :
      ( ( ~ r1_tarski(u1_struct_0(X21),u1_struct_0(X22))
        | m1_pre_topc(X21,X22)
        | ~ m1_pre_topc(X22,X20)
        | ~ m1_pre_topc(X21,X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ m1_pre_topc(X21,X22)
        | r1_tarski(u1_struct_0(X21),u1_struct_0(X22))
        | ~ m1_pre_topc(X22,X20)
        | ~ m1_pre_topc(X21,X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_31,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | ~ l1_pre_topc(esk3_0)
    | ~ l1_pre_topc(esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,u1_struct_0(X2))
    | ~ r1_tsep_1(X3,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X3)
    | ~ r1_tarski(X1,u1_struct_0(X3)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_27])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | ~ l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_tsep_1(X3,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X3)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_34])).

cnf(c_0_44,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_34]),c_0_41])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tsep_1(X1,X2)
    | ~ r1_tsep_1(X3,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ m1_pre_topc(X4,esk1_0)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X1,X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,plain,
    ( m1_pre_topc(X1,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_29])).

cnf(c_0_48,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r1_tsep_1(X1,X2)
    | ~ r1_tsep_1(X3,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ m1_pre_topc(X3,esk3_0)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_35])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_35]),c_0_27]),c_0_32])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( r1_tsep_1(X1,X2)
    | ~ r1_tsep_1(esk3_0,X2)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | ~ l1_pre_topc(esk3_0)
    | ~ l1_pre_topc(esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_19])).

cnf(c_0_54,negated_conjecture,
    ( r1_tsep_1(X1,X2)
    | ~ r1_tsep_1(esk3_0,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk3_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_19])).

cnf(c_0_55,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | ~ l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_34]),c_0_35])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tsep_1(X1,X2)
    | ~ r1_tsep_1(esk3_0,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_34]),c_0_35])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_34]),c_0_41])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tsep_1(X1,esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_59,negated_conjecture,
    ( r1_tsep_1(X1,esk4_0)
    | ~ l1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk4_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( r1_tsep_1(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_19])).

cnf(c_0_61,negated_conjecture,
    ( r1_tsep_1(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_34]),c_0_41])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tsep_1(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_34])).

cnf(c_0_63,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_62])).

cnf(c_0_64,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_19]),c_0_34])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ r1_tsep_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_66,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_67,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_68,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ l1_pre_topc(esk4_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_19])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_62]),c_0_66]),c_0_67])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_34]),c_0_41])])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_66]),c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:55:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S021N
% 0.20/0.39  # and selection function PSelectAllCondOptimalLit.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t24_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3)))|(r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tmap_1)).
% 0.20/0.39  fof(symmetry_r1_tsep_1, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_struct_0(X2))=>(r1_tsep_1(X1,X2)=>r1_tsep_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 0.20/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.39  fof(t64_xboole_1, axiom, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&r1_tarski(X3,X4))&r1_xboole_0(X2,X4))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_xboole_1)).
% 0.20/0.39  fof(d3_tsep_1, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>(r1_tsep_1(X1,X2)<=>r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 0.20/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.39  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.20/0.39  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.20/0.39  fof(c_0_9, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3)))|(r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))))))))), inference(assume_negation,[status(cth)],[t24_tmap_1])).
% 0.20/0.39  fof(c_0_10, plain, ![X18, X19]:(~l1_struct_0(X18)|~l1_struct_0(X19)|(~r1_tsep_1(X18,X19)|r1_tsep_1(X19,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).
% 0.20/0.39  fof(c_0_11, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(m1_pre_topc(esk2_0,esk3_0)&((r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(esk4_0,esk3_0))&(~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk4_0,esk2_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.20/0.39  cnf(c_0_12, plain, (r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_struct_0(X2)|~r1_tsep_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_13, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  fof(c_0_14, plain, ![X13]:(~l1_pre_topc(X13)|l1_struct_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.39  fof(c_0_15, plain, ![X7, X8, X9, X10]:(~r1_tarski(X7,X8)|~r1_tarski(X9,X10)|~r1_xboole_0(X8,X10)|r1_xboole_0(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_xboole_1])])).
% 0.20/0.39  fof(c_0_16, plain, ![X16, X17]:((~r1_tsep_1(X16,X17)|r1_xboole_0(u1_struct_0(X16),u1_struct_0(X17))|~l1_struct_0(X17)|~l1_struct_0(X16))&(~r1_xboole_0(u1_struct_0(X16),u1_struct_0(X17))|r1_tsep_1(X16,X17)|~l1_struct_0(X17)|~l1_struct_0(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).
% 0.20/0.39  fof(c_0_17, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.39  cnf(c_0_18, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)|~l1_struct_0(esk4_0)|~l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.39  cnf(c_0_19, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  fof(c_0_20, plain, ![X14, X15]:(~l1_pre_topc(X14)|(~m1_pre_topc(X15,X14)|l1_pre_topc(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.39  cnf(c_0_21, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)|~r1_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_22, plain, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_23, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  fof(c_0_24, plain, ![X11, X12]:(~v2_pre_topc(X11)|~l1_pre_topc(X11)|(~m1_pre_topc(X12,X11)|v2_pre_topc(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.20/0.39  cnf(c_0_25, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)|~l1_struct_0(esk4_0)|~l1_pre_topc(esk3_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.39  cnf(c_0_26, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_28, plain, (r1_xboole_0(X1,X2)|~r1_tsep_1(X3,X4)|~l1_struct_0(X4)|~l1_struct_0(X3)|~r1_tarski(X2,u1_struct_0(X4))|~r1_tarski(X1,u1_struct_0(X3))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.39  cnf(c_0_29, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_23])).
% 0.20/0.39  fof(c_0_30, plain, ![X20, X21, X22]:((~r1_tarski(u1_struct_0(X21),u1_struct_0(X22))|m1_pre_topc(X21,X22)|~m1_pre_topc(X22,X20)|~m1_pre_topc(X21,X20)|(~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~m1_pre_topc(X21,X22)|r1_tarski(u1_struct_0(X21),u1_struct_0(X22))|~m1_pre_topc(X22,X20)|~m1_pre_topc(X21,X20)|(~v2_pre_topc(X20)|~l1_pre_topc(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.20/0.39  cnf(c_0_31, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_33, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)|~l1_pre_topc(esk3_0)|~l1_pre_topc(esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_19])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, (l1_pre_topc(X1)|~m1_pre_topc(X1,esk1_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_36, plain, (r1_tsep_1(X1,X2)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_37, plain, (r1_xboole_0(X1,u1_struct_0(X2))|~r1_tsep_1(X3,X2)|~l1_struct_0(X2)|~l1_struct_0(X3)|~r1_tarski(X1,u1_struct_0(X3))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.39  cnf(c_0_38, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_39, negated_conjecture, (v2_pre_topc(X1)|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_27])])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)|~l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_42, plain, (r1_tsep_1(X1,X2)|~r1_tsep_1(X3,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)|~l1_struct_0(X3)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X3))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_34])).
% 0.20/0.39  cnf(c_0_44, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_45, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_34]), c_0_41])])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (r1_tsep_1(X1,X2)|~r1_tsep_1(X3,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)|~l1_struct_0(X3)|~m1_pre_topc(X4,esk1_0)|~m1_pre_topc(X3,X4)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X1,X3)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.39  cnf(c_0_47, plain, (m1_pre_topc(X1,X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_44, c_0_29])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)|~l1_struct_0(esk3_0)|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_12, c_0_45])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (r1_tsep_1(X1,X2)|~r1_tsep_1(X3,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)|~l1_struct_0(X3)|~m1_pre_topc(X3,esk3_0)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,X3)), inference(spm,[status(thm)],[c_0_46, c_0_35])).
% 0.20/0.39  cnf(c_0_50, negated_conjecture, (m1_pre_topc(esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_35]), c_0_27]), c_0_32])])).
% 0.20/0.39  cnf(c_0_51, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)|~l1_struct_0(esk4_0)|~l1_pre_topc(esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_19])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (r1_tsep_1(X1,X2)|~r1_tsep_1(esk3_0,X2)|~l1_struct_0(esk3_0)|~l1_struct_0(X2)|~l1_struct_0(X1)|~m1_pre_topc(X1,esk3_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)|~l1_pre_topc(esk3_0)|~l1_pre_topc(esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_19])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (r1_tsep_1(X1,X2)|~r1_tsep_1(esk3_0,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)|~m1_pre_topc(X1,esk3_0)|~l1_pre_topc(esk3_0)), inference(spm,[status(thm)],[c_0_52, c_0_19])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)|~l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_34]), c_0_35])])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (r1_tsep_1(X1,X2)|~r1_tsep_1(esk3_0,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_34]), c_0_35])])).
% 0.20/0.39  cnf(c_0_57, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_34]), c_0_41])])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, (r1_tsep_1(X1,esk4_0)|~l1_struct_0(esk4_0)|~l1_struct_0(X1)|~m1_pre_topc(X1,esk3_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (r1_tsep_1(X1,esk4_0)|~l1_struct_0(X1)|~m1_pre_topc(X1,esk3_0)|~l1_pre_topc(esk4_0)), inference(spm,[status(thm)],[c_0_58, c_0_19])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (r1_tsep_1(X1,esk4_0)|~m1_pre_topc(X1,esk3_0)|~l1_pre_topc(esk4_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_59, c_0_19])).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (r1_tsep_1(X1,esk4_0)|~m1_pre_topc(X1,esk3_0)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_34]), c_0_41])])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (r1_tsep_1(X1,esk4_0)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,esk1_0)), inference(spm,[status(thm)],[c_0_61, c_0_34])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (r1_tsep_1(esk4_0,X1)|~l1_struct_0(esk4_0)|~l1_struct_0(X1)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,esk1_0)), inference(spm,[status(thm)],[c_0_12, c_0_62])).
% 0.20/0.39  cnf(c_0_64, negated_conjecture, (r1_tsep_1(esk4_0,X1)|~l1_struct_0(esk4_0)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_19]), c_0_34])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (m1_pre_topc(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_67, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_68, negated_conjecture, (r1_tsep_1(esk4_0,X1)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,esk1_0)|~l1_pre_topc(esk4_0)), inference(spm,[status(thm)],[c_0_64, c_0_19])).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, (~r1_tsep_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_62]), c_0_66]), c_0_67])])).
% 0.20/0.39  cnf(c_0_70, negated_conjecture, (r1_tsep_1(esk4_0,X1)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_34]), c_0_41])])).
% 0.20/0.39  cnf(c_0_71, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_66]), c_0_67])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 72
% 0.20/0.39  # Proof object clause steps            : 53
% 0.20/0.39  # Proof object formula steps           : 19
% 0.20/0.39  # Proof object conjectures             : 41
% 0.20/0.39  # Proof object clause conjectures      : 38
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 18
% 0.20/0.39  # Proof object initial formulas used   : 9
% 0.20/0.39  # Proof object generating inferences   : 34
% 0.20/0.39  # Proof object simplifying inferences  : 28
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 9
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 24
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 24
% 0.20/0.39  # Processed clauses                    : 200
% 0.20/0.39  # ...of these trivial                  : 1
% 0.20/0.39  # ...subsumed                          : 53
% 0.20/0.39  # ...remaining for further processing  : 146
% 0.20/0.39  # Other redundant clauses eliminated   : 2
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 26
% 0.20/0.39  # Backward-rewritten                   : 7
% 0.20/0.39  # Generated clauses                    : 584
% 0.20/0.39  # ...of the previous two non-trivial   : 568
% 0.20/0.39  # Contextual simplify-reflections      : 18
% 0.20/0.39  # Paramodulations                      : 582
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 2
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
% 0.20/0.39  # Current number of processed clauses  : 88
% 0.20/0.39  #    Positive orientable unit clauses  : 12
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 5
% 0.20/0.39  #    Non-unit-clauses                  : 71
% 0.20/0.39  # Current number of unprocessed clauses: 363
% 0.20/0.39  # ...number of literals in the above   : 3214
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 56
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 5473
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 1248
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 97
% 0.20/0.39  # Unit Clause-clause subsumption calls : 9
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 2
% 0.20/0.39  # BW rewrite match successes           : 2
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 12004
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.048 s
% 0.20/0.39  # System time              : 0.007 s
% 0.20/0.39  # Total time               : 0.055 s
% 0.20/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
