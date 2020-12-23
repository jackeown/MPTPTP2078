%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1726+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:40 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 702 expanded)
%              Number of clauses        :   44 ( 209 expanded)
%              Number of leaves         :    7 ( 175 expanded)
%              Depth                    :   15
%              Number of atoms          :  468 (9111 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   20 (   7 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tmap_1)).

fof(commutativity_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

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

fof(c_0_7,plain,(
    ! [X18,X19,X20,X21] :
      ( ( r1_tsep_1(X19,X21)
        | ~ r1_tsep_1(X20,X21)
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
      & ( r1_tsep_1(X21,X19)
        | ~ r1_tsep_1(X20,X21)
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
      & ( r1_tsep_1(X19,X21)
        | ~ r1_tsep_1(X21,X20)
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
      & ( r1_tsep_1(X21,X19)
        | ~ r1_tsep_1(X21,X20)
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
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_tmap_1])])])])])).

fof(c_0_8,plain,(
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

cnf(c_0_9,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
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

fof(c_0_13,negated_conjecture,(
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

cnf(c_0_14,plain,
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
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_17,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ r1_tsep_1(k2_tsep_1(X22,X25,X24),X23)
        | ~ m1_pre_topc(X23,X25)
        | r1_tsep_1(X23,X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ r1_tsep_1(k2_tsep_1(X22,X24,X25),X23)
        | ~ m1_pre_topc(X23,X25)
        | r1_tsep_1(X23,X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ r1_tsep_1(k2_tsep_1(X22,X23,X25),X24)
        | ~ m1_pre_topc(X24,X25)
        | r1_tsep_1(X23,X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ r1_tsep_1(k2_tsep_1(X22,X25,X23),X24)
        | ~ m1_pre_topc(X24,X25)
        | r1_tsep_1(X23,X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tmap_1])])])])])).

cnf(c_0_18,plain,
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
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk5_0),k1_tsep_1(esk1_0,esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_27,plain,(
    ! [X6,X7,X8] :
      ( v2_struct_0(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,X6)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,X6)
      | k1_tsep_1(X6,X7,X8) = k1_tsep_1(X6,X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k1_tsep_1])])])).

cnf(c_0_28,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk2_0)
    | r1_tsep_1(esk3_0,esk5_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_35,plain,(
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

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0)
    | r1_tsep_1(esk5_0,esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_20]),c_0_30]),c_0_21]),c_0_31]),c_0_32]),c_0_23])]),c_0_24]),c_0_33]),c_0_34]),c_0_25])).

cnf(c_0_38,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,plain,
    ( m1_pre_topc(X1,k1_tsep_1(X2,X3,X1))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_36])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r1_tsep_1(esk5_0,esk2_0)
    | r1_tsep_1(esk3_0,esk5_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_31]),c_0_32]),c_0_23])]),c_0_24]),c_0_33]),c_0_34])).

cnf(c_0_42,plain,
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
    inference(spm,[status(thm)],[c_0_14,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tsep_1(esk3_0,esk4_0)
    | ~ r1_tsep_1(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0)
    | r1_tsep_1(esk5_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_31]),c_0_32]),c_0_23])]),c_0_24]),c_0_33]),c_0_34])).

cnf(c_0_45,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk4_0)
    | r1_tsep_1(esk3_0,esk5_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_19]),c_0_20]),c_0_22]),c_0_21]),c_0_23])]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_47,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_48,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0)
    | ~ r1_tsep_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_20]),c_0_47]),c_0_22]),c_0_31]),c_0_32]),c_0_23])]),c_0_24]),c_0_33]),c_0_34]),c_0_26]),c_0_48])).

cnf(c_0_50,plain,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ r1_tsep_1(X3,X1)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X2,X4)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_51,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_38]),c_0_31]),c_0_32]),c_0_23])]),c_0_24]),c_0_33]),c_0_34])).

cnf(c_0_52,negated_conjecture,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk3_0,X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_32]),c_0_20]),c_0_23])]),c_0_33]),c_0_24])).

cnf(c_0_53,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_51]),c_0_31]),c_0_32]),c_0_23])]),c_0_24]),c_0_33]),c_0_34])).

cnf(c_0_54,negated_conjecture,
    ( r1_tsep_1(esk5_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_31])]),c_0_34])).

cnf(c_0_55,negated_conjecture,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk5_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X2,esk5_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_31]),c_0_20]),c_0_23])]),c_0_34]),c_0_24])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tsep_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_54]),c_0_21]),c_0_30])]),c_0_25])).

cnf(c_0_57,negated_conjecture,
    ( r1_tsep_1(esk3_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_53]),c_0_32])]),c_0_33])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_22]),c_0_47])]),c_0_26]),
    [proof]).

%------------------------------------------------------------------------------
