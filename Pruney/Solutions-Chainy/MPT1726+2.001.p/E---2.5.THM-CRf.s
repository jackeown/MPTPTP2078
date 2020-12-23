%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:10 EST 2020

% Result     : Theorem 0.63s
% Output     : CNFRefutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 702 expanded)
%              Number of clauses        :   44 ( 209 expanded)
%              Number of leaves         :    8 ( 175 expanded)
%              Depth                    :   12
%              Number of atoms          :  529 (9112 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal clause size      :   48 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_tmap_1,axiom,(
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

fof(c_0_8,plain,(
    ! [X22,X23,X24,X25] :
      ( ( r1_tsep_1(X23,X25)
        | ~ r1_tsep_1(X24,X25)
        | ~ m1_pre_topc(X23,X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( r1_tsep_1(X25,X23)
        | ~ r1_tsep_1(X24,X25)
        | ~ m1_pre_topc(X23,X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( r1_tsep_1(X23,X25)
        | ~ r1_tsep_1(X25,X24)
        | ~ m1_pre_topc(X23,X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( r1_tsep_1(X25,X23)
        | ~ r1_tsep_1(X25,X24)
        | ~ m1_pre_topc(X23,X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_tmap_1])])])])])).

fof(c_0_9,plain,(
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

fof(c_0_10,plain,(
    ! [X15,X16,X17] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X15)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X15)
      | m1_pre_topc(X16,k1_tsep_1(X15,X16,X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tsep_1])])])])).

fof(c_0_11,plain,(
    ! [X6,X7,X8] :
      ( v2_struct_0(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,X6)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,X6)
      | k1_tsep_1(X6,X7,X8) = k1_tsep_1(X6,X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k1_tsep_1])])])).

cnf(c_0_12,plain,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ r1_tsep_1(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X2,X4)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,negated_conjecture,(
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

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,k1_tsep_1(X5,X4,X3))
    | ~ v2_pre_topc(X5)
    | ~ m1_pre_topc(X2,k1_tsep_1(X5,X4,X3))
    | ~ m1_pre_topc(X2,X5)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X3,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ l1_pre_topc(X5) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk1_0)
    & m1_pre_topc(esk2_0,esk3_0)
    & m1_pre_topc(esk4_0,esk5_0)
    & ( r1_tsep_1(esk3_0,esk5_0)
      | r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk5_0),k1_tsep_1(esk1_0,esk2_0,esk4_0)) )
    & ( ~ r1_tsep_1(esk3_0,esk4_0)
      | ~ r1_tsep_1(esk5_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

cnf(c_0_20,plain,
    ( m1_pre_topc(X1,k1_tsep_1(X2,X3,X1))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,plain,(
    ! [X26,X27,X28,X29] :
      ( ( ~ r1_tsep_1(k2_tsep_1(X26,X29,X28),X27)
        | ~ m1_pre_topc(X27,X29)
        | r1_tsep_1(X27,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X26)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X26)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ r1_tsep_1(k2_tsep_1(X26,X28,X29),X27)
        | ~ m1_pre_topc(X27,X29)
        | r1_tsep_1(X27,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X26)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X26)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ r1_tsep_1(k2_tsep_1(X26,X27,X29),X28)
        | ~ m1_pre_topc(X28,X29)
        | r1_tsep_1(X27,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X26)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X26)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ r1_tsep_1(k2_tsep_1(X26,X29,X27),X28)
        | ~ m1_pre_topc(X28,X29)
        | r1_tsep_1(X27,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X26)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X26)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tmap_1])])])])])).

cnf(c_0_22,plain,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ r1_tsep_1(X1,k1_tsep_1(X3,X2,X4))
    | ~ v2_pre_topc(X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk5_0),k1_tsep_1(esk1_0,esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,k1_tsep_1(X3,X4,X2))
    | ~ v2_pre_topc(X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_20])).

cnf(c_0_32,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk2_0)
    | r1_tsep_1(esk3_0,esk5_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_39,plain,(
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

cnf(c_0_40,plain,
    ( r1_tsep_1(X2,X4)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(k2_tsep_1(X1,X2,X3),X4)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk4_0)
    | r1_tsep_1(esk3_0,esk5_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_23]),c_0_24]),c_0_26]),c_0_25]),c_0_27])]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_43,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0)
    | r1_tsep_1(esk5_0,esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_24]),c_0_34]),c_0_25]),c_0_35]),c_0_36]),c_0_27])]),c_0_28]),c_0_37]),c_0_38]),c_0_29])).

cnf(c_0_44,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_24]),c_0_42]),c_0_26]),c_0_35]),c_0_36]),c_0_27])]),c_0_28]),c_0_37]),c_0_38]),c_0_30])).

fof(c_0_46,plain,(
    ! [X18,X19,X20,X21] :
      ( ( ~ r1_tsep_1(X20,X21)
        | r1_tsep_1(X19,X21)
        | ~ m1_pre_topc(X19,X20)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X18)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ r1_tsep_1(X21,X20)
        | r1_tsep_1(X19,X21)
        | ~ m1_pre_topc(X19,X20)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X18)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ r1_tsep_1(X20,X21)
        | r1_tsep_1(X21,X19)
        | ~ m1_pre_topc(X19,X20)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X18)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ r1_tsep_1(X21,X20)
        | r1_tsep_1(X21,X19)
        | ~ m1_pre_topc(X19,X20)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X18)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tmap_1])])])])])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( r1_tsep_1(esk5_0,esk2_0)
    | r1_tsep_1(esk3_0,esk5_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_35]),c_0_36]),c_0_27])]),c_0_28]),c_0_37]),c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(esk3_0,esk5_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_44]),c_0_35]),c_0_36]),c_0_27])]),c_0_28]),c_0_37]),c_0_38])).

cnf(c_0_50,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tsep_1(esk3_0,esk4_0)
    | ~ r1_tsep_1(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0)
    | r1_tsep_1(esk5_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_35]),c_0_36]),c_0_27])]),c_0_28]),c_0_37]),c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_49]),c_0_35]),c_0_36]),c_0_27])]),c_0_28]),c_0_37]),c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_25]),c_0_24]),c_0_27])]),c_0_29]),c_0_28])).

cnf(c_0_55,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( r1_tsep_1(esk5_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_34]),c_0_35]),c_0_36])]),c_0_38]),c_0_37])).

cnf(c_0_57,negated_conjecture,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk5_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X2,esk5_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_35]),c_0_24]),c_0_27])]),c_0_38]),c_0_28])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tsep_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_56])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tsep_1(esk3_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_55]),c_0_36])]),c_0_37])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_26]),c_0_42])]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.63/0.84  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_S0Y
% 0.63/0.84  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.63/0.84  #
% 0.63/0.84  # Preprocessing time       : 0.031 s
% 0.63/0.84  
% 0.63/0.84  # Proof found!
% 0.63/0.84  # SZS status Theorem
% 0.63/0.84  # SZS output start CNFRefutation
% 0.63/0.84  fof(t24_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3)))|(r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tmap_1)).
% 0.63/0.84  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 0.63/0.84  fof(t22_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tsep_1)).
% 0.63/0.84  fof(commutativity_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>k1_tsep_1(X1,X2,X3)=k1_tsep_1(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k1_tsep_1)).
% 0.63/0.84  fof(t35_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X2,X3)&m1_pre_topc(X4,X5))=>((~(r1_tsep_1(X3,X5))&~(r1_tsep_1(k2_tsep_1(X1,X3,X5),k1_tsep_1(X1,X2,X4))))|(r1_tsep_1(X3,X4)&r1_tsep_1(X5,X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tmap_1)).
% 0.63/0.84  fof(t34_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X2,X3))=>((m1_pre_topc(X2,X4)=>(~(r1_tsep_1(k2_tsep_1(X1,X4,X3),X2))&~(r1_tsep_1(k2_tsep_1(X1,X3,X4),X2))))&(m1_pre_topc(X3,X4)=>(~(r1_tsep_1(k2_tsep_1(X1,X2,X4),X3))&~(r1_tsep_1(k2_tsep_1(X1,X4,X2),X3)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tmap_1)).
% 0.63/0.84  fof(dt_k2_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k2_tsep_1(X1,X2,X3)))&v1_pre_topc(k2_tsep_1(X1,X2,X3)))&m1_pre_topc(k2_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 0.63/0.84  fof(t23_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 0.63/0.84  fof(c_0_8, plain, ![X22, X23, X24, X25]:(((r1_tsep_1(X23,X25)|~r1_tsep_1(X24,X25)|~m1_pre_topc(X23,X24)|(v2_struct_0(X25)|~m1_pre_topc(X25,X22))|(v2_struct_0(X24)|~m1_pre_topc(X24,X22))|(v2_struct_0(X23)|~m1_pre_topc(X23,X22))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(r1_tsep_1(X25,X23)|~r1_tsep_1(X24,X25)|~m1_pre_topc(X23,X24)|(v2_struct_0(X25)|~m1_pre_topc(X25,X22))|(v2_struct_0(X24)|~m1_pre_topc(X24,X22))|(v2_struct_0(X23)|~m1_pre_topc(X23,X22))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))))&((r1_tsep_1(X23,X25)|~r1_tsep_1(X25,X24)|~m1_pre_topc(X23,X24)|(v2_struct_0(X25)|~m1_pre_topc(X25,X22))|(v2_struct_0(X24)|~m1_pre_topc(X24,X22))|(v2_struct_0(X23)|~m1_pre_topc(X23,X22))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(r1_tsep_1(X25,X23)|~r1_tsep_1(X25,X24)|~m1_pre_topc(X23,X24)|(v2_struct_0(X25)|~m1_pre_topc(X25,X22))|(v2_struct_0(X24)|~m1_pre_topc(X24,X22))|(v2_struct_0(X23)|~m1_pre_topc(X23,X22))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_tmap_1])])])])])).
% 0.63/0.84  fof(c_0_9, plain, ![X9, X10, X11]:(((~v2_struct_0(k1_tsep_1(X9,X10,X11))|(v2_struct_0(X9)|~l1_pre_topc(X9)|v2_struct_0(X10)|~m1_pre_topc(X10,X9)|v2_struct_0(X11)|~m1_pre_topc(X11,X9)))&(v1_pre_topc(k1_tsep_1(X9,X10,X11))|(v2_struct_0(X9)|~l1_pre_topc(X9)|v2_struct_0(X10)|~m1_pre_topc(X10,X9)|v2_struct_0(X11)|~m1_pre_topc(X11,X9))))&(m1_pre_topc(k1_tsep_1(X9,X10,X11),X9)|(v2_struct_0(X9)|~l1_pre_topc(X9)|v2_struct_0(X10)|~m1_pre_topc(X10,X9)|v2_struct_0(X11)|~m1_pre_topc(X11,X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 0.63/0.84  fof(c_0_10, plain, ![X15, X16, X17]:(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)|(v2_struct_0(X16)|~m1_pre_topc(X16,X15)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15)|m1_pre_topc(X16,k1_tsep_1(X15,X16,X17))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tsep_1])])])])).
% 0.63/0.84  fof(c_0_11, plain, ![X6, X7, X8]:(v2_struct_0(X6)|~l1_pre_topc(X6)|v2_struct_0(X7)|~m1_pre_topc(X7,X6)|v2_struct_0(X8)|~m1_pre_topc(X8,X6)|k1_tsep_1(X6,X7,X8)=k1_tsep_1(X6,X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k1_tsep_1])])])).
% 0.63/0.84  cnf(c_0_12, plain, (r1_tsep_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X4)|~r1_tsep_1(X1,X3)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X3,X4)|~m1_pre_topc(X2,X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.63/0.84  cnf(c_0_13, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.63/0.84  cnf(c_0_14, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k1_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.63/0.84  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X2,X3)&m1_pre_topc(X4,X5))=>((~(r1_tsep_1(X3,X5))&~(r1_tsep_1(k2_tsep_1(X1,X3,X5),k1_tsep_1(X1,X2,X4))))|(r1_tsep_1(X3,X4)&r1_tsep_1(X5,X2)))))))))), inference(assume_negation,[status(cth)],[t35_tmap_1])).
% 0.63/0.84  cnf(c_0_16, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.63/0.84  cnf(c_0_17, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|k1_tsep_1(X1,X2,X3)=k1_tsep_1(X1,X3,X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.63/0.84  cnf(c_0_18, plain, (r1_tsep_1(X1,X2)|v2_struct_0(X3)|v2_struct_0(X4)|v2_struct_0(X5)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X1,k1_tsep_1(X5,X4,X3))|~v2_pre_topc(X5)|~m1_pre_topc(X2,k1_tsep_1(X5,X4,X3))|~m1_pre_topc(X2,X5)|~m1_pre_topc(X1,X5)|~m1_pre_topc(X3,X5)|~m1_pre_topc(X4,X5)|~l1_pre_topc(X5)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 0.63/0.84  fof(c_0_19, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk1_0))&((m1_pre_topc(esk2_0,esk3_0)&m1_pre_topc(esk4_0,esk5_0))&((r1_tsep_1(esk3_0,esk5_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk5_0),k1_tsep_1(esk1_0,esk2_0,esk4_0)))&(~r1_tsep_1(esk3_0,esk4_0)|~r1_tsep_1(esk5_0,esk2_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.63/0.84  cnf(c_0_20, plain, (m1_pre_topc(X1,k1_tsep_1(X2,X3,X1))|v2_struct_0(X3)|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.63/0.84  fof(c_0_21, plain, ![X26, X27, X28, X29]:(((~r1_tsep_1(k2_tsep_1(X26,X29,X28),X27)|~m1_pre_topc(X27,X29)|r1_tsep_1(X27,X28)|(v2_struct_0(X29)|~m1_pre_topc(X29,X26))|(v2_struct_0(X28)|~m1_pre_topc(X28,X26))|(v2_struct_0(X27)|~m1_pre_topc(X27,X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~r1_tsep_1(k2_tsep_1(X26,X28,X29),X27)|~m1_pre_topc(X27,X29)|r1_tsep_1(X27,X28)|(v2_struct_0(X29)|~m1_pre_topc(X29,X26))|(v2_struct_0(X28)|~m1_pre_topc(X28,X26))|(v2_struct_0(X27)|~m1_pre_topc(X27,X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))))&((~r1_tsep_1(k2_tsep_1(X26,X27,X29),X28)|~m1_pre_topc(X28,X29)|r1_tsep_1(X27,X28)|(v2_struct_0(X29)|~m1_pre_topc(X29,X26))|(v2_struct_0(X28)|~m1_pre_topc(X28,X26))|(v2_struct_0(X27)|~m1_pre_topc(X27,X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~r1_tsep_1(k2_tsep_1(X26,X29,X27),X28)|~m1_pre_topc(X28,X29)|r1_tsep_1(X27,X28)|(v2_struct_0(X29)|~m1_pre_topc(X29,X26))|(v2_struct_0(X28)|~m1_pre_topc(X28,X26))|(v2_struct_0(X27)|~m1_pre_topc(X27,X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tmap_1])])])])])).
% 0.63/0.84  cnf(c_0_22, plain, (r1_tsep_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X4)|~r1_tsep_1(X1,k1_tsep_1(X3,X2,X4))|~v2_pre_topc(X3)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X4,X3)|~l1_pre_topc(X3)), inference(spm,[status(thm)],[c_0_18, c_0_16])).
% 0.63/0.84  cnf(c_0_23, negated_conjecture, (r1_tsep_1(esk3_0,esk5_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk5_0),k1_tsep_1(esk1_0,esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.84  cnf(c_0_24, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.84  cnf(c_0_25, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.84  cnf(c_0_26, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.84  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.84  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.84  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.84  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.84  cnf(c_0_31, plain, (r1_tsep_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X4)|v2_struct_0(X2)|~r1_tsep_1(X1,k1_tsep_1(X3,X4,X2))|~v2_pre_topc(X3)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X4,X3)|~l1_pre_topc(X3)), inference(spm,[status(thm)],[c_0_18, c_0_20])).
% 0.63/0.84  cnf(c_0_32, plain, (r1_tsep_1(X3,X4)|v2_struct_0(X2)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X1)|~r1_tsep_1(k2_tsep_1(X1,X2,X3),X4)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X4,X1)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.63/0.84  cnf(c_0_33, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk2_0)|r1_tsep_1(esk3_0,esk5_0)|v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0))|~m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27])]), c_0_28]), c_0_29]), c_0_30])).
% 0.63/0.84  cnf(c_0_34, negated_conjecture, (m1_pre_topc(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.84  cnf(c_0_35, negated_conjecture, (m1_pre_topc(esk5_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.84  cnf(c_0_36, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.84  cnf(c_0_37, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.84  cnf(c_0_38, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.84  fof(c_0_39, plain, ![X12, X13, X14]:(((~v2_struct_0(k2_tsep_1(X12,X13,X14))|(v2_struct_0(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X12)|v2_struct_0(X14)|~m1_pre_topc(X14,X12)))&(v1_pre_topc(k2_tsep_1(X12,X13,X14))|(v2_struct_0(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X12)|v2_struct_0(X14)|~m1_pre_topc(X14,X12))))&(m1_pre_topc(k2_tsep_1(X12,X13,X14),X12)|(v2_struct_0(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X12)|v2_struct_0(X14)|~m1_pre_topc(X14,X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).
% 0.63/0.84  cnf(c_0_40, plain, (r1_tsep_1(X2,X4)|v2_struct_0(X3)|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(k2_tsep_1(X1,X2,X3),X4)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.63/0.84  cnf(c_0_41, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk4_0)|r1_tsep_1(esk3_0,esk5_0)|v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0))|~m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_23]), c_0_24]), c_0_26]), c_0_25]), c_0_27])]), c_0_28]), c_0_29]), c_0_30])).
% 0.63/0.84  cnf(c_0_42, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.84  cnf(c_0_43, negated_conjecture, (r1_tsep_1(esk3_0,esk5_0)|r1_tsep_1(esk5_0,esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0))|~m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_24]), c_0_34]), c_0_25]), c_0_35]), c_0_36]), c_0_27])]), c_0_28]), c_0_37]), c_0_38]), c_0_29])).
% 0.63/0.84  cnf(c_0_44, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.63/0.84  cnf(c_0_45, negated_conjecture, (r1_tsep_1(esk3_0,esk5_0)|r1_tsep_1(esk3_0,esk4_0)|v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0))|~m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_24]), c_0_42]), c_0_26]), c_0_35]), c_0_36]), c_0_27])]), c_0_28]), c_0_37]), c_0_38]), c_0_30])).
% 0.63/0.84  fof(c_0_46, plain, ![X18, X19, X20, X21]:(((~r1_tsep_1(X20,X21)|r1_tsep_1(X19,X21)|~m1_pre_topc(X19,X20)|(v2_struct_0(X21)|~m1_pre_topc(X21,X18))|(v2_struct_0(X20)|~m1_pre_topc(X20,X18))|(v2_struct_0(X19)|~m1_pre_topc(X19,X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(~r1_tsep_1(X21,X20)|r1_tsep_1(X19,X21)|~m1_pre_topc(X19,X20)|(v2_struct_0(X21)|~m1_pre_topc(X21,X18))|(v2_struct_0(X20)|~m1_pre_topc(X20,X18))|(v2_struct_0(X19)|~m1_pre_topc(X19,X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18))))&((~r1_tsep_1(X20,X21)|r1_tsep_1(X21,X19)|~m1_pre_topc(X19,X20)|(v2_struct_0(X21)|~m1_pre_topc(X21,X18))|(v2_struct_0(X20)|~m1_pre_topc(X20,X18))|(v2_struct_0(X19)|~m1_pre_topc(X19,X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(~r1_tsep_1(X21,X20)|r1_tsep_1(X21,X19)|~m1_pre_topc(X19,X20)|(v2_struct_0(X21)|~m1_pre_topc(X21,X18))|(v2_struct_0(X20)|~m1_pre_topc(X20,X18))|(v2_struct_0(X19)|~m1_pre_topc(X19,X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tmap_1])])])])])).
% 0.63/0.84  cnf(c_0_47, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k2_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.63/0.84  cnf(c_0_48, negated_conjecture, (r1_tsep_1(esk5_0,esk2_0)|r1_tsep_1(esk3_0,esk5_0)|v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_35]), c_0_36]), c_0_27])]), c_0_28]), c_0_37]), c_0_38])).
% 0.63/0.84  cnf(c_0_49, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(esk3_0,esk5_0)|v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_44]), c_0_35]), c_0_36]), c_0_27])]), c_0_28]), c_0_37]), c_0_38])).
% 0.63/0.84  cnf(c_0_50, plain, (r1_tsep_1(X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X4)|~r1_tsep_1(X1,X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X4)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X3,X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.63/0.84  cnf(c_0_51, negated_conjecture, (~r1_tsep_1(esk3_0,esk4_0)|~r1_tsep_1(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.84  cnf(c_0_52, negated_conjecture, (r1_tsep_1(esk3_0,esk5_0)|r1_tsep_1(esk5_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_35]), c_0_36]), c_0_27])]), c_0_28]), c_0_37]), c_0_38])).
% 0.63/0.84  cnf(c_0_53, negated_conjecture, (r1_tsep_1(esk3_0,esk5_0)|r1_tsep_1(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_49]), c_0_35]), c_0_36]), c_0_27])]), c_0_28]), c_0_37]), c_0_38])).
% 0.63/0.84  cnf(c_0_54, negated_conjecture, (r1_tsep_1(X1,esk2_0)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X2,X1)|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_25]), c_0_24]), c_0_27])]), c_0_29]), c_0_28])).
% 0.63/0.84  cnf(c_0_55, negated_conjecture, (r1_tsep_1(esk3_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.63/0.84  cnf(c_0_56, negated_conjecture, (r1_tsep_1(esk5_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_34]), c_0_35]), c_0_36])]), c_0_38]), c_0_37])).
% 0.63/0.84  cnf(c_0_57, negated_conjecture, (r1_tsep_1(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X1,esk5_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X2,esk5_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_35]), c_0_24]), c_0_27])]), c_0_38]), c_0_28])).
% 0.63/0.84  cnf(c_0_58, negated_conjecture, (~r1_tsep_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_56])])).
% 0.63/0.84  cnf(c_0_59, negated_conjecture, (r1_tsep_1(esk3_0,X1)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_55]), c_0_36])]), c_0_37])).
% 0.63/0.84  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_26]), c_0_42])]), c_0_30]), ['proof']).
% 0.63/0.84  # SZS output end CNFRefutation
% 0.63/0.84  # Proof object total steps             : 61
% 0.63/0.84  # Proof object clause steps            : 44
% 0.63/0.84  # Proof object formula steps           : 17
% 0.63/0.84  # Proof object conjectures             : 33
% 0.63/0.84  # Proof object clause conjectures      : 30
% 0.63/0.84  # Proof object formula conjectures     : 3
% 0.63/0.84  # Proof object initial clauses used    : 25
% 0.63/0.84  # Proof object initial formulas used   : 8
% 0.63/0.84  # Proof object generating inferences   : 18
% 0.63/0.84  # Proof object simplifying inferences  : 93
% 0.63/0.84  # Training examples: 0 positive, 0 negative
% 0.63/0.84  # Parsed axioms                        : 8
% 0.63/0.84  # Removed by relevancy pruning/SinE    : 0
% 0.63/0.84  # Initial clauses                      : 35
% 0.63/0.84  # Removed in clause preprocessing      : 0
% 0.63/0.84  # Initial clauses in saturation        : 35
% 0.63/0.84  # Processed clauses                    : 1285
% 0.63/0.84  # ...of these trivial                  : 4
% 0.63/0.84  # ...subsumed                          : 843
% 0.63/0.84  # ...remaining for further processing  : 438
% 0.63/0.84  # Other redundant clauses eliminated   : 0
% 0.63/0.84  # Clauses deleted for lack of memory   : 0
% 0.63/0.84  # Backward-subsumed                    : 128
% 0.63/0.84  # Backward-rewritten                   : 84
% 0.63/0.84  # Generated clauses                    : 3297
% 0.63/0.84  # ...of the previous two non-trivial   : 3218
% 0.63/0.84  # Contextual simplify-reflections      : 95
% 0.63/0.84  # Paramodulations                      : 3297
% 0.63/0.84  # Factorizations                       : 0
% 0.63/0.84  # Equation resolutions                 : 0
% 0.63/0.84  # Propositional unsat checks           : 0
% 0.63/0.84  #    Propositional check models        : 0
% 0.63/0.84  #    Propositional check unsatisfiable : 0
% 0.63/0.84  #    Propositional clauses             : 0
% 0.63/0.84  #    Propositional clauses after purity: 0
% 0.63/0.84  #    Propositional unsat core size     : 0
% 0.63/0.84  #    Propositional preprocessing time  : 0.000
% 0.63/0.84  #    Propositional encoding time       : 0.000
% 0.63/0.84  #    Propositional solver time         : 0.000
% 0.63/0.84  #    Success case prop preproc time    : 0.000
% 0.63/0.84  #    Success case prop encoding time   : 0.000
% 0.63/0.84  #    Success case prop solver time     : 0.000
% 0.63/0.84  # Current number of processed clauses  : 226
% 0.63/0.84  #    Positive orientable unit clauses  : 14
% 0.63/0.84  #    Positive unorientable unit clauses: 0
% 0.63/0.84  #    Negative unit clauses             : 11
% 0.63/0.84  #    Non-unit-clauses                  : 201
% 0.63/0.84  # Current number of unprocessed clauses: 1330
% 0.63/0.84  # ...number of literals in the above   : 12153
% 0.63/0.84  # Current number of archived formulas  : 0
% 0.63/0.84  # Current number of archived clauses   : 212
% 0.63/0.84  # Clause-clause subsumption calls (NU) : 156964
% 0.63/0.84  # Rec. Clause-clause subsumption calls : 27226
% 0.63/0.84  # Non-unit clause-clause subsumptions  : 911
% 0.63/0.84  # Unit Clause-clause subsumption calls : 1452
% 0.63/0.84  # Rewrite failures with RHS unbound    : 0
% 0.63/0.84  # BW rewrite match attempts            : 6
% 0.63/0.84  # BW rewrite match successes           : 6
% 0.63/0.84  # Condensation attempts                : 0
% 0.63/0.84  # Condensation successes               : 0
% 0.63/0.84  # Termbank termtop insertions          : 108809
% 0.63/0.84  
% 0.63/0.84  # -------------------------------------------------
% 0.63/0.84  # User time                : 0.494 s
% 0.63/0.84  # System time              : 0.005 s
% 0.63/0.84  # Total time               : 0.499 s
% 0.63/0.84  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
