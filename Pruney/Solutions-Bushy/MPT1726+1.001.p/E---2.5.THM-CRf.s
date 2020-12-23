%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1726+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:39 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 809 expanded)
%              Number of clauses        :   67 ( 258 expanded)
%              Number of leaves         :   10 ( 196 expanded)
%              Depth                    :   16
%              Number of atoms          :  505 (9517 expanded)
%              Number of equality atoms :    5 (  15 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   48 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t35_tmap_1,conjecture,(
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
                 => ! [X5] :
                      ( ( ~ v2_struct_0(X5)
                        & m1_pre_topc(X5,X1) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X4,X5) )
                       => ( ( ~ r1_tsep_1(X3,X5)
                            & ~ r1_tsep_1(k2_tsep_1(X1,X3,X5),k1_tsep_1(X1,X2,X4)) )
                          | ( r1_tsep_1(X3,X4)
                            & r1_tsep_1(X5,X2) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tmap_1)).

fof(t22_tsep_1,axiom,(
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
             => m1_pre_topc(X2,k1_tsep_1(X1,X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).

fof(commutativity_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(dt_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
        & v1_pre_topc(k1_tsep_1(X1,X2,X3))
        & m1_pre_topc(k1_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

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

fof(t23_tmap_1,axiom,(
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

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t34_tmap_1,axiom,(
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
                   => ( ( m1_pre_topc(X2,X4)
                       => ( ~ r1_tsep_1(k2_tsep_1(X1,X4,X3),X2)
                          & ~ r1_tsep_1(k2_tsep_1(X1,X3,X4),X2) ) )
                      & ( m1_pre_topc(X3,X4)
                       => ( ~ r1_tsep_1(k2_tsep_1(X1,X2,X4),X3)
                          & ~ r1_tsep_1(k2_tsep_1(X1,X4,X2),X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tmap_1)).

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
                   => ! [X5] :
                        ( ( ~ v2_struct_0(X5)
                          & m1_pre_topc(X5,X1) )
                       => ( ( m1_pre_topc(X2,X3)
                            & m1_pre_topc(X4,X5) )
                         => ( ( ~ r1_tsep_1(X3,X5)
                              & ~ r1_tsep_1(k2_tsep_1(X1,X3,X5),k1_tsep_1(X1,X2,X4)) )
                            | ( r1_tsep_1(X3,X4)
                              & r1_tsep_1(X5,X2) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t35_tmap_1])).

fof(c_0_11,plain,(
    ! [X23,X24,X25] :
      ( v2_struct_0(X23)
      | ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | v2_struct_0(X24)
      | ~ m1_pre_topc(X24,X23)
      | v2_struct_0(X25)
      | ~ m1_pre_topc(X25,X23)
      | m1_pre_topc(X24,k1_tsep_1(X23,X24,X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tsep_1])])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk3_0)
    & ~ v2_struct_0(esk6_0)
    & m1_pre_topc(esk6_0,esk3_0)
    & ~ v2_struct_0(esk7_0)
    & m1_pre_topc(esk7_0,esk3_0)
    & m1_pre_topc(esk4_0,esk5_0)
    & m1_pre_topc(esk6_0,esk7_0)
    & ( r1_tsep_1(esk5_0,esk7_0)
      | r1_tsep_1(k2_tsep_1(esk3_0,esk5_0,esk7_0),k1_tsep_1(esk3_0,esk4_0,esk6_0)) )
    & ( ~ r1_tsep_1(esk5_0,esk6_0)
      | ~ r1_tsep_1(esk7_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X6,X7,X8] :
      ( v2_struct_0(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,X6)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,X6)
      | k1_tsep_1(X6,X7,X8) = k1_tsep_1(X6,X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k1_tsep_1])])])).

fof(c_0_14,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v2_struct_0(k1_tsep_1(X9,X10,X11))
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X9) )
      & ( v1_pre_topc(k1_tsep_1(X9,X10,X11))
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X9) )
      & ( m1_pre_topc(k1_tsep_1(X9,X10,X11),X9)
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_25,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v2_struct_0(k2_tsep_1(X12,X13,X14))
        | v2_struct_0(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12) )
      & ( v1_pre_topc(k2_tsep_1(X12,X13,X14))
        | v2_struct_0(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12) )
      & ( m1_pre_topc(k2_tsep_1(X12,X13,X14),X12)
        | v2_struct_0(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

fof(c_0_26,plain,(
    ! [X26,X27,X28,X29] :
      ( ( ~ r1_tsep_1(X28,X29)
        | r1_tsep_1(X27,X29)
        | ~ m1_pre_topc(X27,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X26)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X26)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ r1_tsep_1(X29,X28)
        | r1_tsep_1(X27,X29)
        | ~ m1_pre_topc(X27,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X26)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X26)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ r1_tsep_1(X28,X29)
        | r1_tsep_1(X29,X27)
        | ~ m1_pre_topc(X27,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X26)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X26)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ r1_tsep_1(X29,X28)
        | r1_tsep_1(X29,X27)
        | ~ m1_pre_topc(X27,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X26)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X26)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tmap_1])])])])])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(X1,k1_tsep_1(esk3_0,X1,esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( k1_tsep_1(esk3_0,X1,esk6_0) = k1_tsep_1(esk3_0,esk6_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_18])]),c_0_23]),c_0_20])).

fof(c_0_29,plain,(
    ! [X21,X22] :
      ( ~ l1_struct_0(X21)
      | ~ l1_struct_0(X22)
      | ~ r1_tsep_1(X21,X22)
      | r1_tsep_1(X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

fof(c_0_30,plain,(
    ! [X16,X17] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_pre_topc(X17,X16)
      | l1_pre_topc(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk3_0,X1,esk6_0),esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_22]),c_0_18])]),c_0_23]),c_0_20])).

cnf(c_0_32,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,plain,
    ( r1_tsep_1(X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X3,X4)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(esk6_0,k1_tsep_1(esk3_0,esk6_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_22]),c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( k1_tsep_1(esk3_0,esk6_0,esk4_0) = k1_tsep_1(esk3_0,esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_16]),c_0_19])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( r1_tsep_1(esk5_0,esk7_0)
    | r1_tsep_1(k2_tsep_1(esk3_0,esk5_0,esk7_0),k1_tsep_1(esk3_0,esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_41,plain,(
    ! [X15] :
      ( ~ l1_pre_topc(X15)
      | l1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_42,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk3_0,esk4_0,esk6_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_16]),c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk3_0,X1,esk7_0),esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_18])]),c_0_34]),c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_47,negated_conjecture,
    ( r1_tsep_1(X1,esk6_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(esk6_0,X2)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X2,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_22]),c_0_17]),c_0_18])]),c_0_20]),c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( m1_pre_topc(esk6_0,k1_tsep_1(esk3_0,esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( ~ v2_struct_0(k1_tsep_1(esk3_0,esk4_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_37]),c_0_16]),c_0_22]),c_0_18])]),c_0_19]),c_0_23]),c_0_20])).

cnf(c_0_50,negated_conjecture,
    ( r1_tsep_1(k1_tsep_1(esk3_0,esk4_0,esk6_0),k2_tsep_1(esk3_0,esk5_0,esk7_0))
    | r1_tsep_1(esk5_0,esk7_0)
    | ~ l1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk6_0))
    | ~ l1_struct_0(k2_tsep_1(esk3_0,esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_51,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( l1_pre_topc(k1_tsep_1(esk3_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_18])])).

cnf(c_0_53,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk3_0,esk5_0,esk7_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_54,plain,
    ( r1_tsep_1(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X2,X4)
    | ~ m1_pre_topc(X3,X4)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_55,negated_conjecture,
    ( r1_tsep_1(X1,esk6_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(k1_tsep_1(esk3_0,esk4_0,esk6_0),X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_43])]),c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r1_tsep_1(k1_tsep_1(esk3_0,esk4_0,esk6_0),k2_tsep_1(esk3_0,esk5_0,esk7_0))
    | r1_tsep_1(esk5_0,esk7_0)
    | ~ l1_struct_0(k2_tsep_1(esk3_0,esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_57,negated_conjecture,
    ( l1_pre_topc(k2_tsep_1(esk3_0,esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_53]),c_0_18])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tsep_1(esk6_0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(esk6_0,X2)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_22]),c_0_17]),c_0_18])]),c_0_20]),c_0_23])).

cnf(c_0_59,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_60,plain,(
    ! [X30,X31,X32,X33] :
      ( ( ~ r1_tsep_1(k2_tsep_1(X30,X33,X32),X31)
        | ~ m1_pre_topc(X31,X33)
        | r1_tsep_1(X31,X32)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X30)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( ~ r1_tsep_1(k2_tsep_1(X30,X32,X33),X31)
        | ~ m1_pre_topc(X31,X33)
        | r1_tsep_1(X31,X32)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X30)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( ~ r1_tsep_1(k2_tsep_1(X30,X31,X33),X32)
        | ~ m1_pre_topc(X32,X33)
        | r1_tsep_1(X31,X32)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X30)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( ~ r1_tsep_1(k2_tsep_1(X30,X33,X31),X32)
        | ~ m1_pre_topc(X32,X33)
        | r1_tsep_1(X31,X32)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X30)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tmap_1])])])])])).

cnf(c_0_61,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk3_0,esk5_0,esk7_0),esk6_0)
    | v2_struct_0(k2_tsep_1(esk3_0,esk5_0,esk7_0))
    | ~ r1_tsep_1(k1_tsep_1(esk3_0,esk4_0,esk6_0),k2_tsep_1(esk3_0,esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( r1_tsep_1(k1_tsep_1(esk3_0,esk4_0,esk6_0),k2_tsep_1(esk3_0,esk5_0,esk7_0))
    | r1_tsep_1(esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_51]),c_0_57])])).

cnf(c_0_63,negated_conjecture,
    ( r1_tsep_1(esk6_0,X1)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk7_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_33])]),c_0_34])).

cnf(c_0_64,plain,
    ( r1_tsep_1(X4,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(k2_tsep_1(X1,X2,X3),X4)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk3_0,esk5_0,esk7_0),esk6_0)
    | r1_tsep_1(esk5_0,esk7_0)
    | v2_struct_0(k2_tsep_1(esk3_0,esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( r1_tsep_1(esk6_0,esk5_0)
    | ~ r1_tsep_1(esk5_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_45]),c_0_46])).

cnf(c_0_67,negated_conjecture,
    ( m1_pre_topc(X1,k1_tsep_1(esk3_0,X1,esk6_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_22]),c_0_17]),c_0_18])]),c_0_23]),c_0_20])).

cnf(c_0_68,negated_conjecture,
    ( r1_tsep_1(esk6_0,esk5_0)
    | v2_struct_0(k2_tsep_1(esk3_0,esk5_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_17]),c_0_59]),c_0_22]),c_0_33]),c_0_45]),c_0_18])]),c_0_23]),c_0_34]),c_0_46]),c_0_20]),c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( r1_tsep_1(X1,esk4_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X2,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_16]),c_0_17]),c_0_18])]),c_0_20]),c_0_19])).

cnf(c_0_70,negated_conjecture,
    ( m1_pre_topc(esk4_0,k1_tsep_1(esk3_0,esk4_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_16]),c_0_19])).

cnf(c_0_71,negated_conjecture,
    ( r1_tsep_1(esk5_0,esk6_0)
    | v2_struct_0(k2_tsep_1(esk3_0,esk5_0,esk7_0))
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_45]),c_0_18])])).

cnf(c_0_73,negated_conjecture,
    ( r1_tsep_1(X1,esk4_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(k1_tsep_1(esk3_0,esk4_0,esk6_0),X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_43])]),c_0_49])).

cnf(c_0_74,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_75,negated_conjecture,
    ( r1_tsep_1(esk5_0,esk6_0)
    | v2_struct_0(k2_tsep_1(esk3_0,esk5_0,esk7_0))
    | ~ l1_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_51]),c_0_72])])).

cnf(c_0_76,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_22]),c_0_18])])).

cnf(c_0_77,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk3_0,esk5_0,esk7_0),esk4_0)
    | v2_struct_0(k2_tsep_1(esk3_0,esk5_0,esk7_0))
    | ~ r1_tsep_1(k1_tsep_1(esk3_0,esk4_0,esk6_0),k2_tsep_1(esk3_0,esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_53])).

cnf(c_0_78,negated_conjecture,
    ( r1_tsep_1(X1,esk4_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk5_0,X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_74]),c_0_45])]),c_0_46])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_tsep_1(esk5_0,esk6_0)
    | ~ r1_tsep_1(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_80,negated_conjecture,
    ( r1_tsep_1(esk5_0,esk6_0)
    | v2_struct_0(k2_tsep_1(esk3_0,esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_51]),c_0_76])])).

cnf(c_0_81,plain,
    ( r1_tsep_1(X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(k2_tsep_1(X1,X2,X3),X4)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_82,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk3_0,esk5_0,esk7_0),esk4_0)
    | r1_tsep_1(esk5_0,esk7_0)
    | v2_struct_0(k2_tsep_1(esk3_0,esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_62])).

cnf(c_0_83,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk4_0)
    | ~ r1_tsep_1(esk5_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_33]),c_0_34])).

cnf(c_0_84,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk3_0,esk5_0,esk7_0))
    | ~ r1_tsep_1(esk7_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_86,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk3_0,esk5_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_17]),c_0_74]),c_0_16]),c_0_33]),c_0_45]),c_0_18])]),c_0_19]),c_0_34]),c_0_46]),c_0_20]),c_0_83]),c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_33]),c_0_45]),c_0_18])]),c_0_34]),c_0_46]),c_0_20]),
    [proof]).

%------------------------------------------------------------------------------
