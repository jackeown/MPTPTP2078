%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 442 expanded)
%              Number of clauses        :   51 ( 189 expanded)
%              Number of leaves         :   10 ( 102 expanded)
%              Depth                    :   16
%              Number of atoms          :  233 (2817 expanded)
%              Number of equality atoms :   17 (  48 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_tmap_1,conjecture,(
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
                   => ( ( r1_tsep_1(X2,X4)
                        & r1_tsep_1(X4,X2) )
                      | ( ~ r1_tsep_1(X3,X4)
                        & ~ r1_tsep_1(X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

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

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(c_0_10,negated_conjecture,(
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
                     => ( ( r1_tsep_1(X2,X4)
                          & r1_tsep_1(X4,X2) )
                        | ( ~ r1_tsep_1(X3,X4)
                          & ~ r1_tsep_1(X4,X3) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_tmap_1])).

fof(c_0_11,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(X13,X12)
      | v2_pre_topc(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_13,negated_conjecture,
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
    & ( ~ r1_tsep_1(esk2_0,esk4_0)
      | ~ r1_tsep_1(esk4_0,esk2_0) )
    & ( r1_tsep_1(esk3_0,esk4_0)
      | r1_tsep_1(esk4_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_14,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | l1_pre_topc(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_15,plain,(
    ! [X21,X22,X23] :
      ( ( ~ r1_tarski(u1_struct_0(X22),u1_struct_0(X23))
        | m1_pre_topc(X22,X23)
        | ~ m1_pre_topc(X23,X21)
        | ~ m1_pre_topc(X22,X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ m1_pre_topc(X22,X23)
        | r1_tarski(u1_struct_0(X22),u1_struct_0(X23))
        | ~ m1_pre_topc(X23,X21)
        | ~ m1_pre_topc(X22,X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_26,plain,
    ( m1_pre_topc(X1,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,plain,(
    ! [X7,X8] :
      ( ( ~ r1_xboole_0(X7,X8)
        | k4_xboole_0(X7,X8) = X7 )
      & ( k4_xboole_0(X7,X8) != X7
        | r1_xboole_0(X7,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_28,plain,(
    ! [X17,X18] :
      ( ( ~ r1_tsep_1(X17,X18)
        | r1_xboole_0(u1_struct_0(X17),u1_struct_0(X18))
        | ~ l1_struct_0(X18)
        | ~ l1_struct_0(X17) )
      & ( ~ r1_xboole_0(u1_struct_0(X17),u1_struct_0(X18))
        | r1_tsep_1(X17,X18)
        | ~ l1_struct_0(X18)
        | ~ l1_struct_0(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

fof(c_0_29,plain,(
    ! [X19,X20] :
      ( ~ l1_struct_0(X19)
      | ~ l1_struct_0(X20)
      | ~ r1_tsep_1(X19,X20)
      | r1_tsep_1(X20,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

fof(c_0_30,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | l1_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_31,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(X1,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_18]),c_0_19])])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_39,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | r1_xboole_0(X9,k4_xboole_0(X11,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_24])).

cnf(c_0_42,plain,
    ( k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X1)
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_48,plain,
    ( k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X1)
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_38])).

cnf(c_0_49,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_tsep_1(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_44])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = X1
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,plain,
    ( k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X1)
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | ~ r1_tsep_1(X1,esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(esk2_0),k4_xboole_0(X1,u1_struct_0(esk3_0))) = u1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(esk4_0),u1_struct_0(X1)) = u1_struct_0(esk4_0)
    | ~ r1_tsep_1(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_33])])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk2_0),k4_xboole_0(X1,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk3_0)) = u1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_33])])).

cnf(c_0_62,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_66,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_38]),c_0_50])])).

cnf(c_0_67,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ r1_tsep_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_69,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_38]),c_0_67])])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69])])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_69]),c_0_67])]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:49:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S01BI
% 0.20/0.40  # and selection function PSelectMinOptimalNoXTypePred.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.028 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t23_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 0.20/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.40  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.20/0.40  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.40  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.20/0.40  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.40  fof(d3_tsep_1, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>(r1_tsep_1(X1,X2)<=>r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 0.20/0.40  fof(symmetry_r1_tsep_1, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_struct_0(X2))=>(r1_tsep_1(X1,X2)=>r1_tsep_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 0.20/0.40  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.40  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.20/0.40  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3)))))))))), inference(assume_negation,[status(cth)],[t23_tmap_1])).
% 0.20/0.40  fof(c_0_11, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.40  fof(c_0_12, plain, ![X12, X13]:(~v2_pre_topc(X12)|~l1_pre_topc(X12)|(~m1_pre_topc(X13,X12)|v2_pre_topc(X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.20/0.40  fof(c_0_13, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(m1_pre_topc(esk2_0,esk3_0)&((~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk4_0,esk2_0))&(r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(esk4_0,esk3_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.20/0.40  fof(c_0_14, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_pre_topc(X16,X15)|l1_pre_topc(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.40  fof(c_0_15, plain, ![X21, X22, X23]:((~r1_tarski(u1_struct_0(X22),u1_struct_0(X23))|m1_pre_topc(X22,X23)|~m1_pre_topc(X23,X21)|~m1_pre_topc(X22,X21)|(~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(~m1_pre_topc(X22,X23)|r1_tarski(u1_struct_0(X22),u1_struct_0(X23))|~m1_pre_topc(X23,X21)|~m1_pre_topc(X22,X21)|(~v2_pre_topc(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.20/0.40  cnf(c_0_16, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_17, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_18, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_20, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_21, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_22, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_23, negated_conjecture, (v2_pre_topc(X1)|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.20/0.40  cnf(c_0_24, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_25, negated_conjecture, (l1_pre_topc(X1)|~m1_pre_topc(X1,esk1_0)), inference(spm,[status(thm)],[c_0_20, c_0_19])).
% 0.20/0.40  cnf(c_0_26, plain, (m1_pre_topc(X1,X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.40  fof(c_0_27, plain, ![X7, X8]:((~r1_xboole_0(X7,X8)|k4_xboole_0(X7,X8)=X7)&(k4_xboole_0(X7,X8)!=X7|r1_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.40  fof(c_0_28, plain, ![X17, X18]:((~r1_tsep_1(X17,X18)|r1_xboole_0(u1_struct_0(X17),u1_struct_0(X18))|~l1_struct_0(X18)|~l1_struct_0(X17))&(~r1_xboole_0(u1_struct_0(X17),u1_struct_0(X18))|r1_tsep_1(X17,X18)|~l1_struct_0(X18)|~l1_struct_0(X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).
% 0.20/0.40  fof(c_0_29, plain, ![X19, X20]:(~l1_struct_0(X19)|~l1_struct_0(X20)|(~r1_tsep_1(X19,X20)|r1_tsep_1(X20,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).
% 0.20/0.40  fof(c_0_30, plain, ![X14]:(~l1_pre_topc(X14)|l1_struct_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.40  cnf(c_0_31, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_32, negated_conjecture, (v2_pre_topc(esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (l1_pre_topc(esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (m1_pre_topc(X1,X1)|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_18]), c_0_19])])).
% 0.20/0.40  cnf(c_0_35, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_36, plain, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.40  cnf(c_0_37, plain, (r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_struct_0(X2)|~r1_tsep_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.40  cnf(c_0_38, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  fof(c_0_39, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|r1_xboole_0(X9,k4_xboole_0(X11,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.20/0.40  cnf(c_0_40, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.20/0.40  cnf(c_0_41, negated_conjecture, (m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_24])).
% 0.20/0.40  cnf(c_0_42, plain, (k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2))=u1_struct_0(X1)|~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.40  cnf(c_0_43, plain, (r1_tsep_1(X1,X2)|~r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_45, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_46, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))|~m1_pre_topc(X1,esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (m1_pre_topc(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_48, plain, (k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2))=u1_struct_0(X1)|~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_42, c_0_38])).
% 0.20/0.40  cnf(c_0_49, plain, (r1_tsep_1(X1,X2)|~r1_tsep_1(X2,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_43, c_0_38])).
% 0.20/0.40  cnf(c_0_50, negated_conjecture, (l1_pre_topc(esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_44])).
% 0.20/0.40  cnf(c_0_51, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=X1|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_35, c_0_45])).
% 0.20/0.40  cnf(c_0_52, negated_conjecture, (r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.40  cnf(c_0_53, plain, (k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2))=u1_struct_0(X1)|~r1_tsep_1(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_48, c_0_38])).
% 0.20/0.40  cnf(c_0_54, negated_conjecture, (r1_tsep_1(esk4_0,X1)|~r1_tsep_1(X1,esk4_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.40  cnf(c_0_55, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_56, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_57, negated_conjecture, (k4_xboole_0(u1_struct_0(esk2_0),k4_xboole_0(X1,u1_struct_0(esk3_0)))=u1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.40  cnf(c_0_58, negated_conjecture, (k4_xboole_0(u1_struct_0(esk4_0),u1_struct_0(X1))=u1_struct_0(esk4_0)|~r1_tsep_1(esk4_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_53, c_0_50])).
% 0.20/0.40  cnf(c_0_59, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_33])])).
% 0.20/0.40  cnf(c_0_60, negated_conjecture, (r1_xboole_0(u1_struct_0(esk2_0),k4_xboole_0(X1,u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.40  cnf(c_0_61, negated_conjecture, (k4_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk3_0))=u1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_33])])).
% 0.20/0.40  cnf(c_0_62, plain, (r1_tsep_1(X1,X2)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.40  cnf(c_0_63, negated_conjecture, (r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (r1_tsep_1(esk2_0,esk4_0)|~l1_struct_0(esk4_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (r1_tsep_1(esk2_0,esk4_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_38]), c_0_50])])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (l1_pre_topc(esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_65])).
% 0.20/0.40  cnf(c_0_68, negated_conjecture, (~r1_tsep_1(esk2_0,esk4_0)|~r1_tsep_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_69, negated_conjecture, (r1_tsep_1(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_38]), c_0_67])])).
% 0.20/0.40  cnf(c_0_70, negated_conjecture, (~r1_tsep_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69])])).
% 0.20/0.40  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_69]), c_0_67])]), c_0_70]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 72
% 0.20/0.40  # Proof object clause steps            : 51
% 0.20/0.40  # Proof object formula steps           : 21
% 0.20/0.40  # Proof object conjectures             : 34
% 0.20/0.40  # Proof object clause conjectures      : 31
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 20
% 0.20/0.40  # Proof object initial formulas used   : 10
% 0.20/0.40  # Proof object generating inferences   : 29
% 0.20/0.40  # Proof object simplifying inferences  : 20
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 10
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 26
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 26
% 0.20/0.40  # Processed clauses                    : 342
% 0.20/0.40  # ...of these trivial                  : 4
% 0.20/0.40  # ...subsumed                          : 120
% 0.20/0.40  # ...remaining for further processing  : 217
% 0.20/0.40  # Other redundant clauses eliminated   : 2
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 2
% 0.20/0.40  # Backward-rewritten                   : 2
% 0.20/0.40  # Generated clauses                    : 552
% 0.20/0.40  # ...of the previous two non-trivial   : 496
% 0.20/0.40  # Contextual simplify-reflections      : 7
% 0.20/0.40  # Paramodulations                      : 550
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 2
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 186
% 0.20/0.40  #    Positive orientable unit clauses  : 32
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 5
% 0.20/0.40  #    Non-unit-clauses                  : 149
% 0.20/0.40  # Current number of unprocessed clauses: 205
% 0.20/0.40  # ...number of literals in the above   : 1564
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 29
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 12884
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 3827
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 128
% 0.20/0.40  # Unit Clause-clause subsumption calls : 139
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 4
% 0.20/0.40  # BW rewrite match successes           : 2
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 10556
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.044 s
% 0.20/0.40  # System time              : 0.007 s
% 0.20/0.40  # Total time               : 0.051 s
% 0.20/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
