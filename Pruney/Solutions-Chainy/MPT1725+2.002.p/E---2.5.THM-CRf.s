%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:10 EST 2020

% Result     : Theorem 14.72s
% Output     : CNFRefutation 14.72s
% Verified   : 
% Statistics : Number of formulae       :  111 (3851 expanded)
%              Number of clauses        :   92 (1152 expanded)
%              Number of leaves         :    9 ( 969 expanded)
%              Depth                    :   34
%              Number of atoms          :  799 (51633 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal clause size      :   48 (   6 average)
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

fof(t34_tmap_1,conjecture,(
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

fof(t32_tmap_1,axiom,(
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
                       => m1_pre_topc(k2_tsep_1(X1,X2,X3),k2_tsep_1(X1,X4,X3)) )
                      & ( m1_pre_topc(X3,X4)
                       => m1_pre_topc(k2_tsep_1(X1,X2,X3),k2_tsep_1(X1,X2,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tmap_1)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t22_tmap_1,axiom,(
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
             => ( m1_pre_topc(X2,X3)
               => ( ~ r1_tsep_1(X2,X3)
                  & ~ r1_tsep_1(X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

fof(c_0_9,plain,(
    ! [X16,X17,X18,X19] :
      ( ( r1_tsep_1(X17,X19)
        | ~ r1_tsep_1(X18,X19)
        | ~ m1_pre_topc(X17,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X16)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X16)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X16)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( r1_tsep_1(X19,X17)
        | ~ r1_tsep_1(X18,X19)
        | ~ m1_pre_topc(X17,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X16)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X16)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X16)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( r1_tsep_1(X17,X19)
        | ~ r1_tsep_1(X19,X18)
        | ~ m1_pre_topc(X17,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X16)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X16)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X16)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( r1_tsep_1(X19,X17)
        | ~ r1_tsep_1(X19,X18)
        | ~ m1_pre_topc(X17,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X16)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X16)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X16)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_tmap_1])])])])])).

fof(c_0_10,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v2_struct_0(k2_tsep_1(X8,X9,X10))
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X8) )
      & ( v1_pre_topc(k2_tsep_1(X8,X9,X10))
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X8) )
      & ( m1_pre_topc(k2_tsep_1(X8,X9,X10),X8)
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

fof(c_0_11,negated_conjecture,(
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
                     => ( ( m1_pre_topc(X2,X4)
                         => ( ~ r1_tsep_1(k2_tsep_1(X1,X4,X3),X2)
                            & ~ r1_tsep_1(k2_tsep_1(X1,X3,X4),X2) ) )
                        & ( m1_pre_topc(X3,X4)
                         => ( ~ r1_tsep_1(k2_tsep_1(X1,X2,X4),X3)
                            & ~ r1_tsep_1(k2_tsep_1(X1,X4,X2),X3) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_tmap_1])).

cnf(c_0_12,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X23,X24,X25,X26] :
      ( ( ~ m1_pre_topc(X24,X26)
        | m1_pre_topc(k2_tsep_1(X23,X24,X25),k2_tsep_1(X23,X26,X25))
        | r1_tsep_1(X24,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X23)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X23)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ m1_pre_topc(X25,X26)
        | m1_pre_topc(k2_tsep_1(X23,X24,X25),k2_tsep_1(X23,X24,X26))
        | r1_tsep_1(X24,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X23)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X23)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_tmap_1])])])])])).

fof(c_0_16,plain,(
    ! [X11,X12] :
      ( ~ l1_struct_0(X11)
      | ~ l1_struct_0(X12)
      | ~ r1_tsep_1(X11,X12)
      | r1_tsep_1(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

fof(c_0_17,negated_conjecture,
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
    & ( m1_pre_topc(esk3_0,esk4_0)
      | m1_pre_topc(esk2_0,esk4_0) )
    & ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
      | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
      | m1_pre_topc(esk2_0,esk4_0) )
    & ( m1_pre_topc(esk3_0,esk4_0)
      | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
      | r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0) )
    & ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
      | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
      | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
      | r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).

cnf(c_0_18,plain,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ v2_pre_topc(X5)
    | ~ r1_tsep_1(k2_tsep_1(X5,X3,X4),X1)
    | ~ m1_pre_topc(X2,k2_tsep_1(X5,X3,X4))
    | ~ m1_pre_topc(X2,X5)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X3,X5)
    | ~ l1_pre_topc(X5) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_19,plain,
    ( m1_pre_topc(k2_tsep_1(X3,X1,X4),k2_tsep_1(X3,X2,X4))
    | r1_tsep_1(X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( m1_pre_topc(k2_tsep_1(X3,X4,X1),k2_tsep_1(X3,X4,X2))
    | r1_tsep_1(X4,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_28,plain,(
    ! [X20,X21,X22] :
      ( ( m1_pre_topc(k2_tsep_1(X20,X21,X22),X21)
        | r1_tsep_1(X21,X22)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X20)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_pre_topc(k2_tsep_1(X20,X21,X22),X22)
        | r1_tsep_1(X21,X22)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X20)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_tsep_1])])])])])).

cnf(c_0_29,plain,
    ( r1_tsep_1(X1,k2_tsep_1(X2,X3,X4))
    | r1_tsep_1(X3,X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ v2_pre_topc(X2)
    | ~ r1_tsep_1(k2_tsep_1(X2,X5,X4),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X3,X5)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_13]),c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))
    | m1_pre_topc(esk3_0,esk4_0)
    | ~ l1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk4_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_35,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | l1_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_36,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(X7,X6)
      | l1_pre_topc(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_37,plain,
    ( r1_tsep_1(X1,k2_tsep_1(X2,X3,X4))
    | r1_tsep_1(X3,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ r1_tsep_1(k2_tsep_1(X2,X3,X5),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X4,X5)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_22]),c_0_13]),c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(esk3_0,X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_23]),c_0_24]),c_0_25])]),c_0_26]),c_0_27])).

cnf(c_0_40,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))
    | r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,X1,esk3_0))
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | m1_pre_topc(esk3_0,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ l1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk4_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_24]),c_0_31]),c_0_23]),c_0_32]),c_0_25])]),c_0_26]),c_0_33]),c_0_27]),c_0_34])).

cnf(c_0_42,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,plain,(
    ! [X13,X14,X15] :
      ( ( ~ r1_tsep_1(X14,X15)
        | ~ m1_pre_topc(X14,X15)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ r1_tsep_1(X15,X14)
        | ~ m1_pre_topc(X14,X15)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tmap_1])])])])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,X1))
    | r1_tsep_1(esk2_0,X1)
    | v2_struct_0(X1)
    | m1_pre_topc(esk2_0,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_24]),c_0_23]),c_0_32]),c_0_31]),c_0_25])]),c_0_26]),c_0_27]),c_0_34]),c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(X2,X3,esk3_0))
    | r1_tsep_1(X3,esk3_0)
    | v2_struct_0(k2_tsep_1(X2,X3,esk3_0))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ r1_tsep_1(esk3_0,X1)
    | ~ m1_pre_topc(k2_tsep_1(X2,X3,esk3_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_27])).

cnf(c_0_49,negated_conjecture,
    ( r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))
    | r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,X1,esk3_0))
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | m1_pre_topc(esk3_0,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | l1_pre_topc(k2_tsep_1(X1,X2,X3))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_13])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_23]),c_0_46]),c_0_27]),c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r1_tsep_1(X1,k2_tsep_1(esk1_0,X2,esk3_0))
    | r1_tsep_1(X2,esk3_0)
    | v2_struct_0(k2_tsep_1(esk1_0,X2,esk3_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_13]),c_0_24]),c_0_23]),c_0_25])]),c_0_26]),c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))
    | r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,X1,esk3_0))
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | m1_pre_topc(esk3_0,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_32]),c_0_23]),c_0_25])]),c_0_26]),c_0_27]),c_0_34])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_31]),c_0_25])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | m1_pre_topc(esk2_0,esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,X1,esk3_0))
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(k2_tsep_1(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_31]),c_0_33])).

cnf(c_0_58,negated_conjecture,
    ( r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))
    | r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,X1,esk3_0))
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | m1_pre_topc(esk3_0,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_42]),c_0_55])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | m1_pre_topc(esk2_0,esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_40]),c_0_24]),c_0_23]),c_0_31]),c_0_25])]),c_0_46]),c_0_27]),c_0_33]),c_0_26])).

cnf(c_0_60,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | v2_struct_0(k2_tsep_1(esk1_0,X1,esk3_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk2_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_57]),c_0_33])).

cnf(c_0_61,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_62,negated_conjecture,
    ( r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))
    | m1_pre_topc(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_31]),c_0_46]),c_0_33]),c_0_47])).

cnf(c_0_63,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_13]),c_0_24]),c_0_23]),c_0_25]),c_0_31])]),c_0_26]),c_0_27]),c_0_33])).

cnf(c_0_64,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_65,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_31]),c_0_24]),c_0_23]),c_0_25])]),c_0_46]),c_0_33]),c_0_27]),c_0_26])).

cnf(c_0_66,negated_conjecture,
    ( r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | m1_pre_topc(esk3_0,esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_62]),c_0_33])).

cnf(c_0_67,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_63]),c_0_23]),c_0_31]),c_0_25])]),c_0_27]),c_0_33]),c_0_26])).

cnf(c_0_68,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
    | r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,X1))
    | r1_tsep_1(esk3_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_64]),c_0_24]),c_0_31]),c_0_32]),c_0_23]),c_0_25])]),c_0_26]),c_0_33]),c_0_34]),c_0_27])).

cnf(c_0_69,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_13]),c_0_24]),c_0_31]),c_0_25]),c_0_23])]),c_0_26]),c_0_27]),c_0_33])).

cnf(c_0_70,plain,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X4)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_71,negated_conjecture,
    ( r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | m1_pre_topc(esk3_0,esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_61]),c_0_24]),c_0_23]),c_0_31]),c_0_25])]),c_0_46]),c_0_27]),c_0_33]),c_0_26])).

cnf(c_0_72,negated_conjecture,
    ( r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,X1,esk2_0))
    | r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | m1_pre_topc(esk2_0,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_67]),c_0_24]),c_0_23]),c_0_31]),c_0_32]),c_0_25])]),c_0_26]),c_0_27]),c_0_33]),c_0_34])).

cnf(c_0_73,negated_conjecture,
    ( r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk2_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_31]),c_0_33]),c_0_38])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_tsep_1(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_69]),c_0_23]),c_0_31]),c_0_25])]),c_0_27]),c_0_33]),c_0_26])).

cnf(c_0_75,plain,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ v2_pre_topc(X5)
    | ~ r1_tsep_1(X2,k2_tsep_1(X5,X3,X4))
    | ~ m1_pre_topc(X1,k2_tsep_1(X5,X3,X4))
    | ~ m1_pre_topc(X2,X5)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X3,X5)
    | ~ l1_pre_topc(X5) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_13]),c_0_14])).

cnf(c_0_76,negated_conjecture,
    ( r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | m1_pre_topc(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_13]),c_0_24]),c_0_31]),c_0_25]),c_0_23])]),c_0_26]),c_0_27]),c_0_33])).

cnf(c_0_77,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,X1,esk2_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_pre_topc(esk2_0,esk4_0)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),esk3_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),X2)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_72]),c_0_27])).

cnf(c_0_78,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
    | r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk2_0)) ),
    inference(sr,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_79,plain,
    ( r1_tsep_1(k2_tsep_1(X1,X2,X3),X4)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ r1_tsep_1(X4,k2_tsep_1(X1,X2,X5))
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X5,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X5)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_22]),c_0_13]),c_0_14])).

cnf(c_0_80,negated_conjecture,
    ( r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))
    | m1_pre_topc(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_76]),c_0_23]),c_0_31]),c_0_25])]),c_0_27]),c_0_33]),c_0_26])).

cnf(c_0_81,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0))
    | v2_struct_0(X1)
    | m1_pre_topc(esk2_0,esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk2_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_61]),c_0_23]),c_0_24]),c_0_31]),c_0_25])]),c_0_74]),c_0_27]),c_0_33]),c_0_26]),c_0_47])).

cnf(c_0_82,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk2_0),esk2_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk2_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_78]),c_0_33])).

cnf(c_0_83,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_84,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,X1),esk2_0)
    | r1_tsep_1(esk3_0,X1)
    | v2_struct_0(X1)
    | m1_pre_topc(esk3_0,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_24]),c_0_31]),c_0_32]),c_0_23]),c_0_25])]),c_0_26]),c_0_33]),c_0_34]),c_0_27])).

cnf(c_0_85,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0))
    | m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_13]),c_0_24]),c_0_23]),c_0_25]),c_0_31])]),c_0_26]),c_0_33]),c_0_27])).

cnf(c_0_86,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk2_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_40]),c_0_24]),c_0_31]),c_0_23]),c_0_25])]),c_0_74]),c_0_33]),c_0_27]),c_0_26])).

cnf(c_0_87,negated_conjecture,
    ( r1_tsep_1(esk3_0,X1)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,X1))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_pre_topc(esk3_0,esk4_0)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,X1),esk2_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,X1),X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_33])).

cnf(c_0_88,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_85]),c_0_31]),c_0_23]),c_0_25])]),c_0_33]),c_0_27]),c_0_26])).

cnf(c_0_89,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_13]),c_0_24]),c_0_31]),c_0_25]),c_0_23])]),c_0_26]),c_0_33]),c_0_27])).

cnf(c_0_90,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0))
    | v2_struct_0(X1)
    | m1_pre_topc(esk3_0,esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk2_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_40]),c_0_31]),c_0_88]),c_0_24]),c_0_23]),c_0_25])]),c_0_74]),c_0_33]),c_0_27]),c_0_26])).

cnf(c_0_91,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_89]),c_0_31]),c_0_23]),c_0_25])]),c_0_33]),c_0_27]),c_0_26])).

cnf(c_0_92,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0))
    | m1_pre_topc(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_13]),c_0_24]),c_0_31]),c_0_25]),c_0_23])]),c_0_26]),c_0_33]),c_0_27])).

cnf(c_0_93,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,X1))
    | r1_tsep_1(esk2_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_91]),c_0_24]),c_0_23]),c_0_32]),c_0_31]),c_0_25])]),c_0_26]),c_0_27]),c_0_34]),c_0_33])).

cnf(c_0_94,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_92]),c_0_31]),c_0_23]),c_0_25])]),c_0_33]),c_0_27]),c_0_26])).

cnf(c_0_95,negated_conjecture,
    ( r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_23]),c_0_94])]),c_0_46]),c_0_27])).

cnf(c_0_96,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_95]),c_0_27])).

cnf(c_0_97,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_40]),c_0_24]),c_0_23]),c_0_31]),c_0_25])]),c_0_46]),c_0_27]),c_0_33]),c_0_26])).

cnf(c_0_98,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_13]),c_0_24]),c_0_23]),c_0_25]),c_0_31])]),c_0_26]),c_0_27]),c_0_33])).

cnf(c_0_99,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_98]),c_0_23]),c_0_31]),c_0_25])]),c_0_27]),c_0_33]),c_0_26])).

cnf(c_0_100,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,X1,esk3_0))
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_99]),c_0_24]),c_0_31]),c_0_23]),c_0_32]),c_0_25])]),c_0_26]),c_0_33]),c_0_27]),c_0_34])).

cnf(c_0_101,negated_conjecture,
    ( r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_31]),c_0_88])]),c_0_46]),c_0_33])).

cnf(c_0_102,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_101]),c_0_33])).

cnf(c_0_103,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_61]),c_0_24]),c_0_23]),c_0_31]),c_0_25])]),c_0_46]),c_0_27]),c_0_33]),c_0_26])).

cnf(c_0_104,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_13]),c_0_24]),c_0_31]),c_0_25]),c_0_23])]),c_0_26]),c_0_27]),c_0_33])).

cnf(c_0_105,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_104]),c_0_23]),c_0_31]),c_0_25])]),c_0_27]),c_0_33]),c_0_26])).

cnf(c_0_106,negated_conjecture,
    ( r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,X1,esk2_0))
    | r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_105]),c_0_24]),c_0_23]),c_0_31]),c_0_32]),c_0_25])]),c_0_26]),c_0_27]),c_0_33]),c_0_34])).

cnf(c_0_107,negated_conjecture,
    ( r1_tsep_1(X1,esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,X1,esk2_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),esk3_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),X2)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_106]),c_0_27])).

cnf(c_0_108,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk2_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_61]),c_0_23]),c_0_94]),c_0_24]),c_0_31]),c_0_25])]),c_0_74]),c_0_27]),c_0_33]),c_0_26])).

cnf(c_0_109,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_13]),c_0_24]),c_0_23]),c_0_25]),c_0_31])]),c_0_26]),c_0_33]),c_0_27])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_109]),c_0_31]),c_0_23]),c_0_25])]),c_0_33]),c_0_27]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:37:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 14.72/15.04  # AutoSched0-Mode selected heuristic G_E___092_C01_F1_AE_CS_SP_PS_CO_S0Y
% 14.72/15.04  # and selection function SelectMaxLComplexAvoidPosPred.
% 14.72/15.04  #
% 14.72/15.04  # Preprocessing time       : 0.029 s
% 14.72/15.04  # Presaturation interreduction done
% 14.72/15.04  
% 14.72/15.04  # Proof found!
% 14.72/15.04  # SZS status Theorem
% 14.72/15.04  # SZS output start CNFRefutation
% 14.72/15.04  fof(t24_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3)))|(r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tmap_1)).
% 14.72/15.04  fof(dt_k2_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k2_tsep_1(X1,X2,X3)))&v1_pre_topc(k2_tsep_1(X1,X2,X3)))&m1_pre_topc(k2_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 14.72/15.04  fof(t34_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X2,X3))=>((m1_pre_topc(X2,X4)=>(~(r1_tsep_1(k2_tsep_1(X1,X4,X3),X2))&~(r1_tsep_1(k2_tsep_1(X1,X3,X4),X2))))&(m1_pre_topc(X3,X4)=>(~(r1_tsep_1(k2_tsep_1(X1,X2,X4),X3))&~(r1_tsep_1(k2_tsep_1(X1,X4,X2),X3)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tmap_1)).
% 14.72/15.04  fof(t32_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X2,X3))=>((m1_pre_topc(X2,X4)=>m1_pre_topc(k2_tsep_1(X1,X2,X3),k2_tsep_1(X1,X4,X3)))&(m1_pre_topc(X3,X4)=>m1_pre_topc(k2_tsep_1(X1,X2,X3),k2_tsep_1(X1,X2,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tmap_1)).
% 14.72/15.04  fof(symmetry_r1_tsep_1, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_struct_0(X2))=>(r1_tsep_1(X1,X2)=>r1_tsep_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 14.72/15.04  fof(t30_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>(m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)&m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tsep_1)).
% 14.72/15.04  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 14.72/15.04  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 14.72/15.04  fof(t22_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(m1_pre_topc(X2,X3)=>(~(r1_tsep_1(X2,X3))&~(r1_tsep_1(X3,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tmap_1)).
% 14.72/15.04  fof(c_0_9, plain, ![X16, X17, X18, X19]:(((r1_tsep_1(X17,X19)|~r1_tsep_1(X18,X19)|~m1_pre_topc(X17,X18)|(v2_struct_0(X19)|~m1_pre_topc(X19,X16))|(v2_struct_0(X18)|~m1_pre_topc(X18,X16))|(v2_struct_0(X17)|~m1_pre_topc(X17,X16))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)))&(r1_tsep_1(X19,X17)|~r1_tsep_1(X18,X19)|~m1_pre_topc(X17,X18)|(v2_struct_0(X19)|~m1_pre_topc(X19,X16))|(v2_struct_0(X18)|~m1_pre_topc(X18,X16))|(v2_struct_0(X17)|~m1_pre_topc(X17,X16))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))))&((r1_tsep_1(X17,X19)|~r1_tsep_1(X19,X18)|~m1_pre_topc(X17,X18)|(v2_struct_0(X19)|~m1_pre_topc(X19,X16))|(v2_struct_0(X18)|~m1_pre_topc(X18,X16))|(v2_struct_0(X17)|~m1_pre_topc(X17,X16))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)))&(r1_tsep_1(X19,X17)|~r1_tsep_1(X19,X18)|~m1_pre_topc(X17,X18)|(v2_struct_0(X19)|~m1_pre_topc(X19,X16))|(v2_struct_0(X18)|~m1_pre_topc(X18,X16))|(v2_struct_0(X17)|~m1_pre_topc(X17,X16))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_tmap_1])])])])])).
% 14.72/15.04  fof(c_0_10, plain, ![X8, X9, X10]:(((~v2_struct_0(k2_tsep_1(X8,X9,X10))|(v2_struct_0(X8)|~l1_pre_topc(X8)|v2_struct_0(X9)|~m1_pre_topc(X9,X8)|v2_struct_0(X10)|~m1_pre_topc(X10,X8)))&(v1_pre_topc(k2_tsep_1(X8,X9,X10))|(v2_struct_0(X8)|~l1_pre_topc(X8)|v2_struct_0(X9)|~m1_pre_topc(X9,X8)|v2_struct_0(X10)|~m1_pre_topc(X10,X8))))&(m1_pre_topc(k2_tsep_1(X8,X9,X10),X8)|(v2_struct_0(X8)|~l1_pre_topc(X8)|v2_struct_0(X9)|~m1_pre_topc(X9,X8)|v2_struct_0(X10)|~m1_pre_topc(X10,X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).
% 14.72/15.04  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X2,X3))=>((m1_pre_topc(X2,X4)=>(~(r1_tsep_1(k2_tsep_1(X1,X4,X3),X2))&~(r1_tsep_1(k2_tsep_1(X1,X3,X4),X2))))&(m1_pre_topc(X3,X4)=>(~(r1_tsep_1(k2_tsep_1(X1,X2,X4),X3))&~(r1_tsep_1(k2_tsep_1(X1,X4,X2),X3))))))))))), inference(assume_negation,[status(cth)],[t34_tmap_1])).
% 14.72/15.04  cnf(c_0_12, plain, (r1_tsep_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X4)|~r1_tsep_1(X3,X1)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X3,X4)|~m1_pre_topc(X2,X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 14.72/15.04  cnf(c_0_13, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 14.72/15.04  cnf(c_0_14, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k2_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 14.72/15.04  fof(c_0_15, plain, ![X23, X24, X25, X26]:((~m1_pre_topc(X24,X26)|m1_pre_topc(k2_tsep_1(X23,X24,X25),k2_tsep_1(X23,X26,X25))|r1_tsep_1(X24,X25)|(v2_struct_0(X26)|~m1_pre_topc(X26,X23))|(v2_struct_0(X25)|~m1_pre_topc(X25,X23))|(v2_struct_0(X24)|~m1_pre_topc(X24,X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)))&(~m1_pre_topc(X25,X26)|m1_pre_topc(k2_tsep_1(X23,X24,X25),k2_tsep_1(X23,X24,X26))|r1_tsep_1(X24,X25)|(v2_struct_0(X26)|~m1_pre_topc(X26,X23))|(v2_struct_0(X25)|~m1_pre_topc(X25,X23))|(v2_struct_0(X24)|~m1_pre_topc(X24,X23))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_tmap_1])])])])])).
% 14.72/15.04  fof(c_0_16, plain, ![X11, X12]:(~l1_struct_0(X11)|~l1_struct_0(X12)|(~r1_tsep_1(X11,X12)|r1_tsep_1(X12,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).
% 14.72/15.04  fof(c_0_17, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(~r1_tsep_1(esk2_0,esk3_0)&(((m1_pre_topc(esk3_0,esk4_0)|m1_pre_topc(esk2_0,esk4_0))&(r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|m1_pre_topc(esk2_0,esk4_0)))&((m1_pre_topc(esk3_0,esk4_0)|(r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)))&(r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|(r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).
% 14.72/15.04  cnf(c_0_18, plain, (r1_tsep_1(X1,X2)|v2_struct_0(X3)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X5)|~v2_pre_topc(X5)|~r1_tsep_1(k2_tsep_1(X5,X3,X4),X1)|~m1_pre_topc(X2,k2_tsep_1(X5,X3,X4))|~m1_pre_topc(X2,X5)|~m1_pre_topc(X1,X5)|~m1_pre_topc(X4,X5)|~m1_pre_topc(X3,X5)|~l1_pre_topc(X5)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 14.72/15.04  cnf(c_0_19, plain, (m1_pre_topc(k2_tsep_1(X3,X1,X4),k2_tsep_1(X3,X2,X4))|r1_tsep_1(X1,X4)|v2_struct_0(X2)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X3)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 14.72/15.04  cnf(c_0_20, plain, (r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_struct_0(X2)|~r1_tsep_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 14.72/15.04  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk3_0,esk4_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 14.72/15.04  cnf(c_0_22, plain, (m1_pre_topc(k2_tsep_1(X3,X4,X1),k2_tsep_1(X3,X4,X2))|r1_tsep_1(X4,X1)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X3)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X4,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 14.72/15.04  cnf(c_0_23, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 14.72/15.04  cnf(c_0_24, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 14.72/15.04  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 14.72/15.04  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 14.72/15.04  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 14.72/15.04  fof(c_0_28, plain, ![X20, X21, X22]:((m1_pre_topc(k2_tsep_1(X20,X21,X22),X21)|r1_tsep_1(X21,X22)|(v2_struct_0(X22)|~m1_pre_topc(X22,X20))|(v2_struct_0(X21)|~m1_pre_topc(X21,X20))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(m1_pre_topc(k2_tsep_1(X20,X21,X22),X22)|r1_tsep_1(X21,X22)|(v2_struct_0(X22)|~m1_pre_topc(X22,X20))|(v2_struct_0(X21)|~m1_pre_topc(X21,X20))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_tsep_1])])])])])).
% 14.72/15.04  cnf(c_0_29, plain, (r1_tsep_1(X1,k2_tsep_1(X2,X3,X4))|r1_tsep_1(X3,X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X5)|~v2_pre_topc(X2)|~r1_tsep_1(k2_tsep_1(X2,X5,X4),X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X5,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X3,X5)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_13]), c_0_14])).
% 14.72/15.04  cnf(c_0_30, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))|m1_pre_topc(esk3_0,esk4_0)|~l1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk4_0))|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 14.72/15.04  cnf(c_0_31, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 14.72/15.04  cnf(c_0_32, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 14.72/15.04  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 14.72/15.04  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 14.72/15.04  fof(c_0_35, plain, ![X5]:(~l1_pre_topc(X5)|l1_struct_0(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 14.72/15.04  fof(c_0_36, plain, ![X6, X7]:(~l1_pre_topc(X6)|(~m1_pre_topc(X7,X6)|l1_pre_topc(X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 14.72/15.04  cnf(c_0_37, plain, (r1_tsep_1(X1,k2_tsep_1(X2,X3,X4))|r1_tsep_1(X3,X4)|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X5)|v2_struct_0(X3)|~v2_pre_topc(X2)|~r1_tsep_1(k2_tsep_1(X2,X3,X5),X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X5,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X4,X5)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_22]), c_0_13]), c_0_14])).
% 14.72/15.04  cnf(c_0_38, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|m1_pre_topc(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 14.72/15.04  cnf(c_0_39, negated_conjecture, (r1_tsep_1(X1,X2)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(esk3_0,X1)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_23]), c_0_24]), c_0_25])]), c_0_26]), c_0_27])).
% 14.72/15.04  cnf(c_0_40, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 14.72/15.04  cnf(c_0_41, negated_conjecture, (r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))|r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,X1,esk3_0))|r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|m1_pre_topc(esk3_0,esk4_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)|~l1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk4_0))|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_24]), c_0_31]), c_0_23]), c_0_32]), c_0_25])]), c_0_26]), c_0_33]), c_0_27]), c_0_34])).
% 14.72/15.04  cnf(c_0_42, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 14.72/15.04  cnf(c_0_43, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 14.72/15.04  fof(c_0_44, plain, ![X13, X14, X15]:((~r1_tsep_1(X14,X15)|~m1_pre_topc(X14,X15)|(v2_struct_0(X15)|~m1_pre_topc(X15,X13))|(v2_struct_0(X14)|~m1_pre_topc(X14,X13))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)))&(~r1_tsep_1(X15,X14)|~m1_pre_topc(X14,X15)|(v2_struct_0(X15)|~m1_pre_topc(X15,X13))|(v2_struct_0(X14)|~m1_pre_topc(X14,X13))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tmap_1])])])])])).
% 14.72/15.04  cnf(c_0_45, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,X1))|r1_tsep_1(esk2_0,X1)|v2_struct_0(X1)|m1_pre_topc(esk2_0,esk4_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_24]), c_0_23]), c_0_32]), c_0_31]), c_0_25])]), c_0_26]), c_0_27]), c_0_34]), c_0_33])).
% 14.72/15.04  cnf(c_0_46, negated_conjecture, (~r1_tsep_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 14.72/15.04  cnf(c_0_47, negated_conjecture, (m1_pre_topc(esk3_0,esk4_0)|m1_pre_topc(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 14.72/15.04  cnf(c_0_48, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(X2,X3,esk3_0))|r1_tsep_1(X3,esk3_0)|v2_struct_0(k2_tsep_1(X2,X3,esk3_0))|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X1)|~v2_pre_topc(X2)|~r1_tsep_1(esk3_0,X1)|~m1_pre_topc(k2_tsep_1(X2,X3,esk3_0),esk1_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(esk3_0,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_27])).
% 14.72/15.04  cnf(c_0_49, negated_conjecture, (r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))|r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,X1,esk3_0))|r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|m1_pre_topc(esk3_0,esk4_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)|~l1_struct_0(esk2_0)|~l1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 14.72/15.04  cnf(c_0_50, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|l1_pre_topc(k2_tsep_1(X1,X2,X3))|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_43, c_0_13])).
% 14.72/15.04  cnf(c_0_51, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tsep_1(X1,X2)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 14.72/15.04  cnf(c_0_52, negated_conjecture, (r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|m1_pre_topc(esk2_0,esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_23]), c_0_46]), c_0_27]), c_0_47])).
% 14.72/15.04  cnf(c_0_53, negated_conjecture, (r1_tsep_1(X1,k2_tsep_1(esk1_0,X2,esk3_0))|r1_tsep_1(X2,esk3_0)|v2_struct_0(k2_tsep_1(esk1_0,X2,esk3_0))|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(esk3_0,X1)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_13]), c_0_24]), c_0_23]), c_0_25])]), c_0_26]), c_0_27])).
% 14.72/15.04  cnf(c_0_54, negated_conjecture, (r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))|r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,X1,esk3_0))|r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|m1_pre_topc(esk3_0,esk4_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_32]), c_0_23]), c_0_25])]), c_0_26]), c_0_27]), c_0_34])).
% 14.72/15.04  cnf(c_0_55, negated_conjecture, (l1_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_31]), c_0_25])])).
% 14.72/15.04  cnf(c_0_56, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|m1_pre_topc(esk2_0,esk4_0)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_27])).
% 14.72/15.04  cnf(c_0_57, negated_conjecture, (r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,X1,esk3_0))|r1_tsep_1(X1,esk3_0)|v2_struct_0(k2_tsep_1(esk1_0,X1,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(esk3_0,esk2_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_31]), c_0_33])).
% 14.72/15.04  cnf(c_0_58, negated_conjecture, (r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))|r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,X1,esk3_0))|r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|m1_pre_topc(esk3_0,esk4_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_42]), c_0_55])])).
% 14.72/15.04  cnf(c_0_59, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|m1_pre_topc(esk2_0,esk4_0)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_40]), c_0_24]), c_0_23]), c_0_31]), c_0_25])]), c_0_46]), c_0_27]), c_0_33]), c_0_26])).
% 14.72/15.04  cnf(c_0_60, negated_conjecture, (r1_tsep_1(X1,esk3_0)|v2_struct_0(k2_tsep_1(esk1_0,X1,esk3_0))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X2)|~r1_tsep_1(esk3_0,esk2_0)|~m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk2_0)|~m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),X2)|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X1,esk1_0)|~l1_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_57]), c_0_33])).
% 14.72/15.04  cnf(c_0_61, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 14.72/15.04  cnf(c_0_62, negated_conjecture, (r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))|m1_pre_topc(esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_31]), c_0_46]), c_0_33]), c_0_47])).
% 14.72/15.04  cnf(c_0_63, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_13]), c_0_24]), c_0_23]), c_0_25]), c_0_31])]), c_0_26]), c_0_27]), c_0_33])).
% 14.72/15.04  cnf(c_0_64, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 14.72/15.04  cnf(c_0_65, negated_conjecture, (v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~r1_tsep_1(esk3_0,esk2_0)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_31]), c_0_24]), c_0_23]), c_0_25])]), c_0_46]), c_0_33]), c_0_27]), c_0_26])).
% 14.72/15.04  cnf(c_0_66, negated_conjecture, (r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|m1_pre_topc(esk3_0,esk4_0)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_62]), c_0_33])).
% 14.72/15.04  cnf(c_0_67, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_63]), c_0_23]), c_0_31]), c_0_25])]), c_0_27]), c_0_33]), c_0_26])).
% 14.72/15.04  cnf(c_0_68, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)|r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,X1))|r1_tsep_1(esk3_0,X1)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_64]), c_0_24]), c_0_31]), c_0_32]), c_0_23]), c_0_25])]), c_0_26]), c_0_33]), c_0_34]), c_0_27])).
% 14.72/15.04  cnf(c_0_69, negated_conjecture, (v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_13]), c_0_24]), c_0_31]), c_0_25]), c_0_23])]), c_0_26]), c_0_27]), c_0_33])).
% 14.72/15.04  cnf(c_0_70, plain, (r1_tsep_1(X1,X2)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X1)|v2_struct_0(X4)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X2,X4)|~m1_pre_topc(X3,X4)|~m1_pre_topc(X1,X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 14.72/15.04  cnf(c_0_71, negated_conjecture, (r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|m1_pre_topc(esk3_0,esk4_0)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_61]), c_0_24]), c_0_23]), c_0_31]), c_0_25])]), c_0_46]), c_0_27]), c_0_33]), c_0_26])).
% 14.72/15.04  cnf(c_0_72, negated_conjecture, (r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,X1,esk2_0))|r1_tsep_1(X1,esk2_0)|v2_struct_0(X1)|m1_pre_topc(esk2_0,esk4_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_67]), c_0_24]), c_0_23]), c_0_31]), c_0_32]), c_0_25])]), c_0_26]), c_0_27]), c_0_33]), c_0_34])).
% 14.72/15.04  cnf(c_0_73, negated_conjecture, (r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk2_0))|r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(esk3_0,esk2_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_31]), c_0_33]), c_0_38])).
% 14.72/15.04  cnf(c_0_74, negated_conjecture, (~r1_tsep_1(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_69]), c_0_23]), c_0_31]), c_0_25])]), c_0_27]), c_0_33]), c_0_26])).
% 14.72/15.04  cnf(c_0_75, plain, (r1_tsep_1(X1,X2)|v2_struct_0(X3)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X5)|~v2_pre_topc(X5)|~r1_tsep_1(X2,k2_tsep_1(X5,X3,X4))|~m1_pre_topc(X1,k2_tsep_1(X5,X3,X4))|~m1_pre_topc(X2,X5)|~m1_pre_topc(X1,X5)|~m1_pre_topc(X4,X5)|~m1_pre_topc(X3,X5)|~l1_pre_topc(X5)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_13]), c_0_14])).
% 14.72/15.04  cnf(c_0_76, negated_conjecture, (r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|m1_pre_topc(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_13]), c_0_24]), c_0_31]), c_0_25]), c_0_23])]), c_0_26]), c_0_27]), c_0_33])).
% 14.72/15.04  cnf(c_0_77, negated_conjecture, (r1_tsep_1(X1,esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,X1,esk2_0))|v2_struct_0(X1)|v2_struct_0(X2)|m1_pre_topc(esk2_0,esk4_0)|~v2_pre_topc(X2)|~m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),esk3_0)|~m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),X2)|~m1_pre_topc(esk3_0,X2)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)|~l1_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_72]), c_0_27])).
% 14.72/15.04  cnf(c_0_78, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)|r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk2_0))), inference(sr,[status(thm)],[c_0_73, c_0_74])).
% 14.72/15.04  cnf(c_0_79, plain, (r1_tsep_1(k2_tsep_1(X1,X2,X3),X4)|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X5)|v2_struct_0(X2)|~v2_pre_topc(X1)|~r1_tsep_1(X4,k2_tsep_1(X1,X2,X5))|~m1_pre_topc(X4,X1)|~m1_pre_topc(X5,X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X3,X5)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_22]), c_0_13]), c_0_14])).
% 14.72/15.04  cnf(c_0_80, negated_conjecture, (r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk3_0,esk4_0))|m1_pre_topc(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_76]), c_0_23]), c_0_31]), c_0_25])]), c_0_27]), c_0_33]), c_0_26])).
% 14.72/15.04  cnf(c_0_81, negated_conjecture, (v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0))|v2_struct_0(X1)|m1_pre_topc(esk2_0,esk4_0)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk2_0),X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_61]), c_0_23]), c_0_24]), c_0_31]), c_0_25])]), c_0_74]), c_0_27]), c_0_33]), c_0_26]), c_0_47])).
% 14.72/15.04  cnf(c_0_82, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk2_0),esk2_0)|~m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk2_0),X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_78]), c_0_33])).
% 14.72/15.04  cnf(c_0_83, plain, (v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X3)|~r1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 14.72/15.04  cnf(c_0_84, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,X1),esk2_0)|r1_tsep_1(esk3_0,X1)|v2_struct_0(X1)|m1_pre_topc(esk3_0,esk4_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_24]), c_0_31]), c_0_32]), c_0_23]), c_0_25])]), c_0_26]), c_0_33]), c_0_34]), c_0_27])).
% 14.72/15.04  cnf(c_0_85, negated_conjecture, (v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0))|m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_13]), c_0_24]), c_0_23]), c_0_25]), c_0_31])]), c_0_26]), c_0_33]), c_0_27])).
% 14.72/15.04  cnf(c_0_86, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)|v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk2_0),X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_40]), c_0_24]), c_0_31]), c_0_23]), c_0_25])]), c_0_74]), c_0_33]), c_0_27]), c_0_26])).
% 14.72/15.04  cnf(c_0_87, negated_conjecture, (r1_tsep_1(esk3_0,X1)|v2_struct_0(k2_tsep_1(esk1_0,esk3_0,X1))|v2_struct_0(X1)|v2_struct_0(X2)|m1_pre_topc(esk3_0,esk4_0)|~v2_pre_topc(X2)|~m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,X1),esk2_0)|~m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,X1),X2)|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)|~l1_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_33])).
% 14.72/15.04  cnf(c_0_88, negated_conjecture, (m1_pre_topc(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_85]), c_0_31]), c_0_23]), c_0_25])]), c_0_33]), c_0_27]), c_0_26])).
% 14.72/15.04  cnf(c_0_89, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_13]), c_0_24]), c_0_31]), c_0_25]), c_0_23])]), c_0_26]), c_0_33]), c_0_27])).
% 14.72/15.04  cnf(c_0_90, negated_conjecture, (v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0))|v2_struct_0(X1)|m1_pre_topc(esk3_0,esk4_0)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk2_0),X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_40]), c_0_31]), c_0_88]), c_0_24]), c_0_23]), c_0_25])]), c_0_74]), c_0_33]), c_0_27]), c_0_26])).
% 14.72/15.04  cnf(c_0_91, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_89]), c_0_31]), c_0_23]), c_0_25])]), c_0_33]), c_0_27]), c_0_26])).
% 14.72/15.04  cnf(c_0_92, negated_conjecture, (v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0))|m1_pre_topc(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_13]), c_0_24]), c_0_31]), c_0_25]), c_0_23])]), c_0_26]), c_0_33]), c_0_27])).
% 14.72/15.04  cnf(c_0_93, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,X1))|r1_tsep_1(esk2_0,X1)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_91]), c_0_24]), c_0_23]), c_0_32]), c_0_31]), c_0_25])]), c_0_26]), c_0_27]), c_0_34]), c_0_33])).
% 14.72/15.04  cnf(c_0_94, negated_conjecture, (m1_pre_topc(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_92]), c_0_31]), c_0_23]), c_0_25])]), c_0_33]), c_0_27]), c_0_26])).
% 14.72/15.04  cnf(c_0_95, negated_conjecture, (r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_23]), c_0_94])]), c_0_46]), c_0_27])).
% 14.72/15.04  cnf(c_0_96, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_95]), c_0_27])).
% 14.72/15.04  cnf(c_0_97, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_40]), c_0_24]), c_0_23]), c_0_31]), c_0_25])]), c_0_46]), c_0_27]), c_0_33]), c_0_26])).
% 14.72/15.04  cnf(c_0_98, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_13]), c_0_24]), c_0_23]), c_0_25]), c_0_31])]), c_0_26]), c_0_27]), c_0_33])).
% 14.72/15.04  cnf(c_0_99, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk3_0),esk2_0)|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_98]), c_0_23]), c_0_31]), c_0_25])]), c_0_27]), c_0_33]), c_0_26])).
% 14.72/15.04  cnf(c_0_100, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,X1,esk3_0))|r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_99]), c_0_24]), c_0_31]), c_0_23]), c_0_32]), c_0_25])]), c_0_26]), c_0_33]), c_0_27]), c_0_34])).
% 14.72/15.04  cnf(c_0_101, negated_conjecture, (r1_tsep_1(esk2_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_31]), c_0_88])]), c_0_46]), c_0_33])).
% 14.72/15.04  cnf(c_0_102, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_101]), c_0_33])).
% 14.72/15.04  cnf(c_0_103, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_61]), c_0_24]), c_0_23]), c_0_31]), c_0_25])]), c_0_46]), c_0_27]), c_0_33]), c_0_26])).
% 14.72/15.04  cnf(c_0_104, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_13]), c_0_24]), c_0_31]), c_0_25]), c_0_23])]), c_0_26]), c_0_27]), c_0_33])).
% 14.72/15.04  cnf(c_0_105, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_104]), c_0_23]), c_0_31]), c_0_25])]), c_0_27]), c_0_33]), c_0_26])).
% 14.72/15.04  cnf(c_0_106, negated_conjecture, (r1_tsep_1(esk3_0,k2_tsep_1(esk1_0,X1,esk2_0))|r1_tsep_1(X1,esk2_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_105]), c_0_24]), c_0_23]), c_0_31]), c_0_32]), c_0_25])]), c_0_26]), c_0_27]), c_0_33]), c_0_34])).
% 14.72/15.05  cnf(c_0_107, negated_conjecture, (r1_tsep_1(X1,esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,X1,esk2_0))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X2)|~m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),esk3_0)|~m1_pre_topc(k2_tsep_1(esk1_0,X1,esk2_0),X2)|~m1_pre_topc(esk3_0,X2)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)|~l1_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_106]), c_0_27])).
% 14.72/15.05  cnf(c_0_108, negated_conjecture, (v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk2_0),X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_61]), c_0_23]), c_0_94]), c_0_24]), c_0_31]), c_0_25])]), c_0_74]), c_0_27]), c_0_33]), c_0_26])).
% 14.72/15.05  cnf(c_0_109, negated_conjecture, (v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_13]), c_0_24]), c_0_23]), c_0_25]), c_0_31])]), c_0_26]), c_0_33]), c_0_27])).
% 14.72/15.05  cnf(c_0_110, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_109]), c_0_31]), c_0_23]), c_0_25])]), c_0_33]), c_0_27]), c_0_26]), ['proof']).
% 14.72/15.05  # SZS output end CNFRefutation
% 14.78/15.05  # Proof object total steps             : 111
% 14.78/15.05  # Proof object clause steps            : 92
% 14.78/15.05  # Proof object formula steps           : 19
% 14.78/15.05  # Proof object conjectures             : 76
% 14.78/15.05  # Proof object clause conjectures      : 73
% 14.78/15.05  # Proof object formula conjectures     : 3
% 14.78/15.05  # Proof object initial clauses used    : 27
% 14.78/15.05  # Proof object initial formulas used   : 9
% 14.78/15.05  # Proof object generating inferences   : 64
% 14.78/15.05  # Proof object simplifying inferences  : 357
% 14.78/15.05  # Training examples: 0 positive, 0 negative
% 14.78/15.05  # Parsed axioms                        : 9
% 14.78/15.05  # Removed by relevancy pruning/SinE    : 0
% 14.78/15.05  # Initial clauses                      : 30
% 14.78/15.05  # Removed in clause preprocessing      : 0
% 14.78/15.05  # Initial clauses in saturation        : 30
% 14.78/15.05  # Processed clauses                    : 23924
% 14.78/15.05  # ...of these trivial                  : 1
% 14.78/15.05  # ...subsumed                          : 17243
% 14.78/15.05  # ...remaining for further processing  : 6680
% 14.78/15.05  # Other redundant clauses eliminated   : 0
% 14.78/15.05  # Clauses deleted for lack of memory   : 0
% 14.78/15.05  # Backward-subsumed                    : 3609
% 14.78/15.05  # Backward-rewritten                   : 652
% 14.78/15.05  # Generated clauses                    : 123598
% 14.78/15.05  # ...of the previous two non-trivial   : 123468
% 14.78/15.05  # Contextual simplify-reflections      : 1670
% 14.78/15.05  # Paramodulations                      : 123595
% 14.78/15.05  # Factorizations                       : 0
% 14.78/15.05  # Equation resolutions                 : 0
% 14.78/15.05  # Propositional unsat checks           : 0
% 14.78/15.05  #    Propositional check models        : 0
% 14.78/15.05  #    Propositional check unsatisfiable : 0
% 14.78/15.05  #    Propositional clauses             : 0
% 14.78/15.05  #    Propositional clauses after purity: 0
% 14.78/15.05  #    Propositional unsat core size     : 0
% 14.78/15.05  #    Propositional preprocessing time  : 0.000
% 14.78/15.05  #    Propositional encoding time       : 0.000
% 14.78/15.05  #    Propositional solver time         : 0.000
% 14.78/15.05  #    Success case prop preproc time    : 0.000
% 14.78/15.05  #    Success case prop encoding time   : 0.000
% 14.78/15.05  #    Success case prop solver time     : 0.000
% 14.78/15.05  # Current number of processed clauses  : 2386
% 14.78/15.05  #    Positive orientable unit clauses  : 12
% 14.78/15.05  #    Positive unorientable unit clauses: 0
% 14.78/15.05  #    Negative unit clauses             : 13
% 14.78/15.05  #    Non-unit-clauses                  : 2361
% 14.78/15.05  # Current number of unprocessed clauses: 91383
% 14.78/15.05  # ...number of literals in the above   : 1601198
% 14.78/15.05  # Current number of archived formulas  : 0
% 14.78/15.05  # Current number of archived clauses   : 4294
% 14.78/15.05  # Clause-clause subsumption calls (NU) : 8781289
% 14.78/15.05  # Rec. Clause-clause subsumption calls : 343864
% 14.78/15.05  # Non-unit clause-clause subsumptions  : 17306
% 14.78/15.05  # Unit Clause-clause subsumption calls : 11132
% 14.78/15.05  # Rewrite failures with RHS unbound    : 0
% 14.78/15.05  # BW rewrite match attempts            : 12
% 14.78/15.05  # BW rewrite match successes           : 4
% 14.78/15.05  # Condensation attempts                : 23924
% 14.78/15.05  # Condensation successes               : 0
% 14.78/15.05  # Termbank termtop insertions          : 12031864
% 14.78/15.05  
% 14.78/15.05  # -------------------------------------------------
% 14.78/15.05  # User time                : 14.496 s
% 14.78/15.05  # System time              : 0.109 s
% 14.78/15.05  # Total time               : 14.605 s
% 14.78/15.05  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
