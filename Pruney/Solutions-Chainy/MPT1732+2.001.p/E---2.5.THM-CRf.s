%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:11 EST 2020

% Result     : Theorem 0.76s
% Output     : CNFRefutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   75 (1834 expanded)
%              Number of clauses        :   56 ( 668 expanded)
%              Number of leaves         :    9 ( 448 expanded)
%              Depth                    :   21
%              Number of atoms          :  292 (17438 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_tmap_1,conjecture,(
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
                 => ( ~ r1_tsep_1(X2,X3)
                   => ( ( ~ r1_tsep_1(k2_tsep_1(X1,X2,X3),X4)
                       => ( ~ r1_tsep_1(X2,X4)
                          & ~ r1_tsep_1(X3,X4) ) )
                      & ( ~ r1_tsep_1(X4,k2_tsep_1(X1,X2,X3))
                       => ( ~ r1_tsep_1(X4,X2)
                          & ~ r1_tsep_1(X4,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

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

fof(t30_tsep_1,axiom,(
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
               => ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)
                  & m1_pre_topc(k2_tsep_1(X1,X2,X3),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tsep_1)).

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

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

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

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
                   => ( ~ r1_tsep_1(X2,X3)
                     => ( ( ~ r1_tsep_1(k2_tsep_1(X1,X2,X3),X4)
                         => ( ~ r1_tsep_1(X2,X4)
                            & ~ r1_tsep_1(X3,X4) ) )
                        & ( ~ r1_tsep_1(X4,k2_tsep_1(X1,X2,X3))
                         => ( ~ r1_tsep_1(X4,X2)
                            & ~ r1_tsep_1(X4,X3) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_tmap_1])).

fof(c_0_10,plain,(
    ! [X9,X10] :
      ( ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(X10,X9)
      | l1_pre_topc(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

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
    & ~ r1_tsep_1(esk2_0,esk3_0)
    & ( ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( r1_tsep_1(esk4_0,esk2_0)
      | r1_tsep_1(esk4_0,esk3_0)
      | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk2_0,esk4_0)
      | r1_tsep_1(esk3_0,esk4_0) )
    & ( r1_tsep_1(esk4_0,esk2_0)
      | r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk2_0,esk4_0)
      | r1_tsep_1(esk3_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).

fof(c_0_12,plain,(
    ! [X8] :
      ( ~ l1_pre_topc(X8)
      | l1_struct_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_13,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X16,X17] :
      ( ~ l1_struct_0(X16)
      | ~ l1_struct_0(X17)
      | ~ r1_tsep_1(X16,X17)
      | r1_tsep_1(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

cnf(c_0_18,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_16]),c_0_15])])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_21]),c_0_15])])).

cnf(c_0_27,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_28,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_26])).

fof(c_0_29,plain,(
    ! [X13,X14,X15] :
      ( ( ~ v2_struct_0(k2_tsep_1(X13,X14,X15))
        | v2_struct_0(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13) )
      & ( v1_pre_topc(k2_tsep_1(X13,X14,X15))
        | v2_struct_0(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13) )
      & ( m1_pre_topc(k2_tsep_1(X13,X14,X15),X13)
        | v2_struct_0(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

fof(c_0_30,plain,(
    ! [X18,X19,X20] :
      ( ( m1_pre_topc(k2_tsep_1(X18,X19,X20),X19)
        | r1_tsep_1(X19,X20)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_pre_topc(k2_tsep_1(X18,X19,X20),X20)
        | r1_tsep_1(X19,X20)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_tsep_1])])])])])).

fof(c_0_31,plain,(
    ! [X11,X12] :
      ( ( ~ r1_tsep_1(X11,X12)
        | r1_xboole_0(u1_struct_0(X11),u1_struct_0(X12))
        | ~ l1_struct_0(X12)
        | ~ l1_struct_0(X11) )
      & ( ~ r1_xboole_0(u1_struct_0(X11),u1_struct_0(X12))
        | r1_tsep_1(X11,X12)
        | ~ l1_struct_0(X12)
        | ~ l1_struct_0(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_27]),c_0_24]),c_0_28])])).

fof(c_0_33,plain,(
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

cnf(c_0_34,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_39,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_40,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_32]),c_0_25]),c_0_24])])).

cnf(c_0_42,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_16]),c_0_15])]),c_0_35]),c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,negated_conjecture,
    ( v2_struct_0(X1)
    | r1_tsep_1(X1,esk3_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk3_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_16]),c_0_38]),c_0_15])]),c_0_35]),c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_24]),c_0_25])])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_16]),c_0_38]),c_0_15])])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_21]),c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_21]),c_0_44]),c_0_46])).

cnf(c_0_52,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_53,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_xboole_0(X1,u1_struct_0(esk4_0))
    | ~ r1_tarski(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_50]),c_0_15])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tsep_1(X1,esk4_0)
    | ~ l1_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( l1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_61,negated_conjecture,
    ( r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_59]),c_0_24]),c_0_58])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_59])).

cnf(c_0_63,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_64,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_62]),c_0_28]),c_0_24])])).

cnf(c_0_65,negated_conjecture,
    ( v2_struct_0(X1)
    | r1_tsep_1(X1,esk3_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_16]),c_0_38]),c_0_15])]),c_0_35]),c_0_36])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_64]),c_0_24]),c_0_28])])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_21]),c_0_38]),c_0_15])])).

cnf(c_0_68,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_21]),c_0_44]),c_0_46])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(X1,u1_struct_0(esk4_0))
    | ~ r1_tarski(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_50]),c_0_68])])).

cnf(c_0_71,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_72,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_71]),c_0_58])])).

cnf(c_0_73,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_72])])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_72]),c_0_24]),c_0_58])]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.76/0.97  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S047A
% 0.76/0.97  # and selection function PSelectComplexPreferNEQ.
% 0.76/0.97  #
% 0.76/0.97  # Preprocessing time       : 0.028 s
% 0.76/0.97  # Presaturation interreduction done
% 0.76/0.97  
% 0.76/0.97  # Proof found!
% 0.76/0.97  # SZS status Theorem
% 0.76/0.97  # SZS output start CNFRefutation
% 0.76/0.97  fof(t41_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X2,X3))=>((~(r1_tsep_1(k2_tsep_1(X1,X2,X3),X4))=>(~(r1_tsep_1(X2,X4))&~(r1_tsep_1(X3,X4))))&(~(r1_tsep_1(X4,k2_tsep_1(X1,X2,X3)))=>(~(r1_tsep_1(X4,X2))&~(r1_tsep_1(X4,X3)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tmap_1)).
% 0.76/0.97  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.76/0.97  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.76/0.97  fof(symmetry_r1_tsep_1, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_struct_0(X2))=>(r1_tsep_1(X1,X2)=>r1_tsep_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 0.76/0.97  fof(dt_k2_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k2_tsep_1(X1,X2,X3)))&v1_pre_topc(k2_tsep_1(X1,X2,X3)))&m1_pre_topc(k2_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 0.76/0.97  fof(t30_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>(m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)&m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tsep_1)).
% 0.76/0.97  fof(d3_tsep_1, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>(r1_tsep_1(X1,X2)<=>r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 0.76/0.97  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.76/0.97  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.76/0.97  fof(c_0_9, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X2,X3))=>((~(r1_tsep_1(k2_tsep_1(X1,X2,X3),X4))=>(~(r1_tsep_1(X2,X4))&~(r1_tsep_1(X3,X4))))&(~(r1_tsep_1(X4,k2_tsep_1(X1,X2,X3)))=>(~(r1_tsep_1(X4,X2))&~(r1_tsep_1(X4,X3))))))))))), inference(assume_negation,[status(cth)],[t41_tmap_1])).
% 0.76/0.97  fof(c_0_10, plain, ![X9, X10]:(~l1_pre_topc(X9)|(~m1_pre_topc(X10,X9)|l1_pre_topc(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.76/0.97  fof(c_0_11, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(~r1_tsep_1(esk2_0,esk3_0)&(((~r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0))&(r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)))&((~r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk3_0,esk4_0)))&(r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk3_0,esk4_0)))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).
% 0.76/0.97  fof(c_0_12, plain, ![X8]:(~l1_pre_topc(X8)|l1_struct_0(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.76/0.97  cnf(c_0_13, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.76/0.97  cnf(c_0_14, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.76/0.97  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.76/0.97  cnf(c_0_16, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.76/0.97  fof(c_0_17, plain, ![X16, X17]:(~l1_struct_0(X16)|~l1_struct_0(X17)|(~r1_tsep_1(X16,X17)|r1_tsep_1(X17,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).
% 0.76/0.97  cnf(c_0_18, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.76/0.97  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.76/0.97  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_16]), c_0_15])])).
% 0.76/0.97  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.76/0.97  cnf(c_0_22, plain, (r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_struct_0(X2)|~r1_tsep_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.76/0.97  cnf(c_0_23, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.76/0.97  cnf(c_0_24, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.76/0.97  cnf(c_0_25, negated_conjecture, (l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_18, c_0_20])).
% 0.76/0.97  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_21]), c_0_15])])).
% 0.76/0.97  cnf(c_0_27, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])])).
% 0.76/0.97  cnf(c_0_28, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_18, c_0_26])).
% 0.76/0.97  fof(c_0_29, plain, ![X13, X14, X15]:(((~v2_struct_0(k2_tsep_1(X13,X14,X15))|(v2_struct_0(X13)|~l1_pre_topc(X13)|v2_struct_0(X14)|~m1_pre_topc(X14,X13)|v2_struct_0(X15)|~m1_pre_topc(X15,X13)))&(v1_pre_topc(k2_tsep_1(X13,X14,X15))|(v2_struct_0(X13)|~l1_pre_topc(X13)|v2_struct_0(X14)|~m1_pre_topc(X14,X13)|v2_struct_0(X15)|~m1_pre_topc(X15,X13))))&(m1_pre_topc(k2_tsep_1(X13,X14,X15),X13)|(v2_struct_0(X13)|~l1_pre_topc(X13)|v2_struct_0(X14)|~m1_pre_topc(X14,X13)|v2_struct_0(X15)|~m1_pre_topc(X15,X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).
% 0.76/0.97  fof(c_0_30, plain, ![X18, X19, X20]:((m1_pre_topc(k2_tsep_1(X18,X19,X20),X19)|r1_tsep_1(X19,X20)|(v2_struct_0(X20)|~m1_pre_topc(X20,X18))|(v2_struct_0(X19)|~m1_pre_topc(X19,X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(m1_pre_topc(k2_tsep_1(X18,X19,X20),X20)|r1_tsep_1(X19,X20)|(v2_struct_0(X20)|~m1_pre_topc(X20,X18))|(v2_struct_0(X19)|~m1_pre_topc(X19,X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_tsep_1])])])])])).
% 0.76/0.97  fof(c_0_31, plain, ![X11, X12]:((~r1_tsep_1(X11,X12)|r1_xboole_0(u1_struct_0(X11),u1_struct_0(X12))|~l1_struct_0(X12)|~l1_struct_0(X11))&(~r1_xboole_0(u1_struct_0(X11),u1_struct_0(X12))|r1_tsep_1(X11,X12)|~l1_struct_0(X12)|~l1_struct_0(X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).
% 0.76/0.97  cnf(c_0_32, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_27]), c_0_24]), c_0_28])])).
% 0.76/0.97  fof(c_0_33, plain, ![X21, X22, X23]:((~r1_tarski(u1_struct_0(X22),u1_struct_0(X23))|m1_pre_topc(X22,X23)|~m1_pre_topc(X23,X21)|~m1_pre_topc(X22,X21)|(~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(~m1_pre_topc(X22,X23)|r1_tarski(u1_struct_0(X22),u1_struct_0(X23))|~m1_pre_topc(X23,X21)|~m1_pre_topc(X22,X21)|(~v2_pre_topc(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.76/0.97  cnf(c_0_34, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.76/0.97  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.76/0.97  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.76/0.97  cnf(c_0_37, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.76/0.97  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.76/0.97  fof(c_0_39, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_xboole_0(X6,X7)|r1_xboole_0(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.76/0.97  cnf(c_0_40, plain, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.76/0.97  cnf(c_0_41, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_32]), c_0_25]), c_0_24])])).
% 0.76/0.97  cnf(c_0_42, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.76/0.97  cnf(c_0_43, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_16]), c_0_15])]), c_0_35]), c_0_36])).
% 0.76/0.97  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.76/0.97  cnf(c_0_45, negated_conjecture, (v2_struct_0(X1)|r1_tsep_1(X1,esk3_0)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk3_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_16]), c_0_38]), c_0_15])]), c_0_35]), c_0_36])).
% 0.76/0.97  cnf(c_0_46, negated_conjecture, (~r1_tsep_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.76/0.97  cnf(c_0_47, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.76/0.97  cnf(c_0_48, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_24]), c_0_25])])).
% 0.76/0.97  cnf(c_0_49, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_16]), c_0_38]), c_0_15])])).
% 0.76/0.97  cnf(c_0_50, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_21]), c_0_44])).
% 0.76/0.97  cnf(c_0_51, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_21]), c_0_44]), c_0_46])).
% 0.76/0.97  cnf(c_0_52, plain, (r1_tsep_1(X1,X2)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.76/0.97  cnf(c_0_53, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_xboole_0(X1,u1_struct_0(esk4_0))|~r1_tarski(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.76/0.97  cnf(c_0_54, negated_conjecture, (r1_tarski(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])])).
% 0.76/0.97  cnf(c_0_55, negated_conjecture, (l1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_50]), c_0_15])])).
% 0.76/0.97  cnf(c_0_56, negated_conjecture, (r1_tsep_1(X1,esk4_0)|~l1_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_52, c_0_24])).
% 0.76/0.97  cnf(c_0_57, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.76/0.97  cnf(c_0_58, negated_conjecture, (l1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_18, c_0_55])).
% 0.76/0.97  cnf(c_0_59, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|r1_tsep_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 0.76/0.97  cnf(c_0_60, negated_conjecture, (~r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.76/0.97  cnf(c_0_61, negated_conjecture, (r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_59]), c_0_24]), c_0_58])])).
% 0.76/0.97  cnf(c_0_62, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_59])).
% 0.76/0.97  cnf(c_0_63, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.76/0.97  cnf(c_0_64, negated_conjecture, (r1_tsep_1(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_62]), c_0_28]), c_0_24])])).
% 0.76/0.97  cnf(c_0_65, negated_conjecture, (v2_struct_0(X1)|r1_tsep_1(X1,esk3_0)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_16]), c_0_38]), c_0_15])]), c_0_35]), c_0_36])).
% 0.76/0.97  cnf(c_0_66, negated_conjecture, (r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_64]), c_0_24]), c_0_28])])).
% 0.76/0.97  cnf(c_0_67, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_21]), c_0_38]), c_0_15])])).
% 0.76/0.97  cnf(c_0_68, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_21]), c_0_44]), c_0_46])).
% 0.76/0.97  cnf(c_0_69, negated_conjecture, (r1_xboole_0(X1,u1_struct_0(esk4_0))|~r1_tarski(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_47, c_0_66])).
% 0.76/0.97  cnf(c_0_70, negated_conjecture, (r1_tarski(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_50]), c_0_68])])).
% 0.76/0.97  cnf(c_0_71, negated_conjecture, (r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.76/0.97  cnf(c_0_72, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_71]), c_0_58])])).
% 0.76/0.97  cnf(c_0_73, negated_conjecture, (~r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_72])])).
% 0.76/0.97  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_72]), c_0_24]), c_0_58])]), c_0_73]), ['proof']).
% 0.76/0.97  # SZS output end CNFRefutation
% 0.76/0.97  # Proof object total steps             : 75
% 0.76/0.97  # Proof object clause steps            : 56
% 0.76/0.97  # Proof object formula steps           : 19
% 0.76/0.97  # Proof object conjectures             : 49
% 0.76/0.97  # Proof object clause conjectures      : 46
% 0.76/0.97  # Proof object formula conjectures     : 3
% 0.76/0.97  # Proof object initial clauses used    : 21
% 0.76/0.97  # Proof object initial formulas used   : 9
% 0.76/0.97  # Proof object generating inferences   : 34
% 0.76/0.97  # Proof object simplifying inferences  : 69
% 0.76/0.97  # Training examples: 0 positive, 0 negative
% 0.76/0.97  # Parsed axioms                        : 9
% 0.76/0.97  # Removed by relevancy pruning/SinE    : 0
% 0.76/0.97  # Initial clauses                      : 27
% 0.76/0.97  # Removed in clause preprocessing      : 0
% 0.76/0.97  # Initial clauses in saturation        : 27
% 0.76/0.97  # Processed clauses                    : 3090
% 0.76/0.97  # ...of these trivial                  : 1
% 0.76/0.97  # ...subsumed                          : 210
% 0.76/0.97  # ...remaining for further processing  : 2878
% 0.76/0.97  # Other redundant clauses eliminated   : 0
% 0.76/0.97  # Clauses deleted for lack of memory   : 0
% 0.76/0.97  # Backward-subsumed                    : 173
% 0.76/0.97  # Backward-rewritten                   : 806
% 0.76/0.97  # Generated clauses                    : 38057
% 0.76/0.97  # ...of the previous two non-trivial   : 37956
% 0.76/0.97  # Contextual simplify-reflections      : 11
% 0.76/0.97  # Paramodulations                      : 37971
% 0.76/0.97  # Factorizations                       : 86
% 0.76/0.97  # Equation resolutions                 : 0
% 0.76/0.97  # Propositional unsat checks           : 0
% 0.76/0.97  #    Propositional check models        : 0
% 0.76/0.97  #    Propositional check unsatisfiable : 0
% 0.76/0.97  #    Propositional clauses             : 0
% 0.76/0.97  #    Propositional clauses after purity: 0
% 0.76/0.97  #    Propositional unsat core size     : 0
% 0.76/0.97  #    Propositional preprocessing time  : 0.000
% 0.76/0.97  #    Propositional encoding time       : 0.000
% 0.76/0.97  #    Propositional solver time         : 0.000
% 0.76/0.97  #    Success case prop preproc time    : 0.000
% 0.76/0.97  #    Success case prop encoding time   : 0.000
% 0.76/0.97  #    Success case prop solver time     : 0.000
% 0.76/0.97  # Current number of processed clauses  : 1872
% 0.76/0.97  #    Positive orientable unit clauses  : 1226
% 0.76/0.97  #    Positive unorientable unit clauses: 0
% 0.76/0.97  #    Negative unit clauses             : 6
% 0.76/0.97  #    Non-unit-clauses                  : 640
% 0.76/0.97  # Current number of unprocessed clauses: 34704
% 0.76/0.97  # ...number of literals in the above   : 116026
% 0.76/0.97  # Current number of archived formulas  : 0
% 0.76/0.97  # Current number of archived clauses   : 1006
% 0.76/0.97  # Clause-clause subsumption calls (NU) : 80075
% 0.76/0.97  # Rec. Clause-clause subsumption calls : 32205
% 0.76/0.97  # Non-unit clause-clause subsumptions  : 343
% 0.76/0.97  # Unit Clause-clause subsumption calls : 92533
% 0.76/0.97  # Rewrite failures with RHS unbound    : 0
% 0.76/0.97  # BW rewrite match attempts            : 112689
% 0.76/0.97  # BW rewrite match successes           : 408
% 0.76/0.97  # Condensation attempts                : 0
% 0.76/0.97  # Condensation successes               : 0
% 0.76/0.97  # Termbank termtop insertions          : 1760763
% 0.76/0.97  
% 0.76/0.97  # -------------------------------------------------
% 0.76/0.97  # User time                : 0.599 s
% 0.76/0.97  # System time              : 0.027 s
% 0.76/0.97  # Total time               : 0.626 s
% 0.76/0.97  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
