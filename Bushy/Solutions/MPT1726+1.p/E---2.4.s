%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t35_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:14 EDT 2019

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   86 (1419 expanded)
%              Number of clauses        :   63 ( 438 expanded)
%              Number of leaves         :   11 ( 347 expanded)
%              Depth                    :   21
%              Number of atoms          :  566 (16996 expanded)
%              Number of equality atoms :    5 (  50 expanded)
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',t35_tmap_1)).

fof(commutativity_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',commutativity_k1_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',dt_k1_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',dt_k2_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',t24_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',t22_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',t34_tmap_1)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',symmetry_r1_tsep_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t35_tmap_1.p',t23_tmap_1)).

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

fof(c_0_12,plain,(
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ m1_pre_topc(X15,X14)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | k1_tsep_1(X14,X15,X16) = k1_tsep_1(X14,X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k1_tsep_1])])])).

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
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk1_0)
    & m1_pre_topc(esk2_0,esk3_0)
    & m1_pre_topc(esk4_0,esk5_0)
    & ( r1_tsep_1(esk3_0,esk5_0)
      | r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk5_0),k1_tsep_1(esk1_0,esk2_0,esk4_0)) )
    & ( ~ r1_tsep_1(esk3_0,esk4_0)
      | ~ r1_tsep_1(esk5_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | k1_tsep_1(X1,X2,X3) = k1_tsep_1(X1,X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X19,X20,X21] :
      ( ( ~ v2_struct_0(k1_tsep_1(X19,X20,X21))
        | v2_struct_0(X19)
        | ~ l1_pre_topc(X19)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X19)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19) )
      & ( v1_pre_topc(k1_tsep_1(X19,X20,X21))
        | v2_struct_0(X19)
        | ~ l1_pre_topc(X19)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X19)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19) )
      & ( m1_pre_topc(k1_tsep_1(X19,X20,X21),X19)
        | v2_struct_0(X19)
        | ~ l1_pre_topc(X19)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X19)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

cnf(c_0_20,negated_conjecture,
    ( k1_tsep_1(esk1_0,X1,esk2_0) = k1_tsep_1(esk1_0,esk2_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])]),c_0_17]),c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_23,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v2_struct_0(k2_tsep_1(X22,X23,X24))
        | v2_struct_0(X22)
        | ~ l1_pre_topc(X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22) )
      & ( v1_pre_topc(k2_tsep_1(X22,X23,X24))
        | v2_struct_0(X22)
        | ~ l1_pre_topc(X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22) )
      & ( m1_pre_topc(k2_tsep_1(X22,X23,X24),X22)
        | v2_struct_0(X22)
        | ~ l1_pre_topc(X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

fof(c_0_24,plain,(
    ! [X50,X51,X52,X53] :
      ( ( r1_tsep_1(X51,X53)
        | ~ r1_tsep_1(X52,X53)
        | ~ m1_pre_topc(X51,X52)
        | v2_struct_0(X53)
        | ~ m1_pre_topc(X53,X50)
        | v2_struct_0(X52)
        | ~ m1_pre_topc(X52,X50)
        | v2_struct_0(X51)
        | ~ m1_pre_topc(X51,X50)
        | v2_struct_0(X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50) )
      & ( r1_tsep_1(X53,X51)
        | ~ r1_tsep_1(X52,X53)
        | ~ m1_pre_topc(X51,X52)
        | v2_struct_0(X53)
        | ~ m1_pre_topc(X53,X50)
        | v2_struct_0(X52)
        | ~ m1_pre_topc(X52,X50)
        | v2_struct_0(X51)
        | ~ m1_pre_topc(X51,X50)
        | v2_struct_0(X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50) )
      & ( r1_tsep_1(X51,X53)
        | ~ r1_tsep_1(X53,X52)
        | ~ m1_pre_topc(X51,X52)
        | v2_struct_0(X53)
        | ~ m1_pre_topc(X53,X50)
        | v2_struct_0(X52)
        | ~ m1_pre_topc(X52,X50)
        | v2_struct_0(X51)
        | ~ m1_pre_topc(X51,X50)
        | v2_struct_0(X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50) )
      & ( r1_tsep_1(X53,X51)
        | ~ r1_tsep_1(X53,X52)
        | ~ m1_pre_topc(X51,X52)
        | v2_struct_0(X53)
        | ~ m1_pre_topc(X53,X50)
        | v2_struct_0(X52)
        | ~ m1_pre_topc(X52,X50)
        | v2_struct_0(X51)
        | ~ m1_pre_topc(X51,X50)
        | v2_struct_0(X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_tmap_1])])])])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( k1_tsep_1(esk1_0,esk4_0,esk2_0) = k1_tsep_1(esk1_0,esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_27,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_30,plain,(
    ! [X43,X44,X45] :
      ( v2_struct_0(X43)
      | ~ v2_pre_topc(X43)
      | ~ l1_pre_topc(X43)
      | v2_struct_0(X44)
      | ~ m1_pre_topc(X44,X43)
      | v2_struct_0(X45)
      | ~ m1_pre_topc(X45,X43)
      | m1_pre_topc(X44,k1_tsep_1(X43,X44,X45)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tsep_1])])])])).

cnf(c_0_31,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk5_0),k1_tsep_1(esk1_0,esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(k1_tsep_1(esk1_0,esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_15]),c_0_21]),c_0_16])]),c_0_17]),c_0_22]),c_0_18])).

cnf(c_0_34,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,X1,esk5_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_16])]),c_0_17]),c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk5_0),X1)
    | r1_tsep_1(esk3_0,esk5_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),X2)
    | ~ m1_pre_topc(X1,k1_tsep_1(esk1_0,esk2_0,esk4_0))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk5_0),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,esk2_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_26]),c_0_15]),c_0_21]),c_0_16])]),c_0_17]),c_0_22]),c_0_18])).

cnf(c_0_42,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( m1_pre_topc(X1,k1_tsep_1(esk1_0,X1,esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_21]),c_0_16]),c_0_39])]),c_0_17]),c_0_22])).

fof(c_0_44,plain,(
    ! [X56,X57,X58,X59] :
      ( ( ~ r1_tsep_1(k2_tsep_1(X56,X59,X58),X57)
        | ~ m1_pre_topc(X57,X59)
        | r1_tsep_1(X57,X58)
        | v2_struct_0(X59)
        | ~ m1_pre_topc(X59,X56)
        | v2_struct_0(X58)
        | ~ m1_pre_topc(X58,X56)
        | v2_struct_0(X57)
        | ~ m1_pre_topc(X57,X56)
        | v2_struct_0(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56) )
      & ( ~ r1_tsep_1(k2_tsep_1(X56,X58,X59),X57)
        | ~ m1_pre_topc(X57,X59)
        | r1_tsep_1(X57,X58)
        | v2_struct_0(X59)
        | ~ m1_pre_topc(X59,X56)
        | v2_struct_0(X58)
        | ~ m1_pre_topc(X58,X56)
        | v2_struct_0(X57)
        | ~ m1_pre_topc(X57,X56)
        | v2_struct_0(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56) )
      & ( ~ r1_tsep_1(k2_tsep_1(X56,X57,X59),X58)
        | ~ m1_pre_topc(X58,X59)
        | r1_tsep_1(X57,X58)
        | v2_struct_0(X59)
        | ~ m1_pre_topc(X59,X56)
        | v2_struct_0(X58)
        | ~ m1_pre_topc(X58,X56)
        | v2_struct_0(X57)
        | ~ m1_pre_topc(X57,X56)
        | v2_struct_0(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56) )
      & ( ~ r1_tsep_1(k2_tsep_1(X56,X59,X57),X58)
        | ~ m1_pre_topc(X58,X59)
        | r1_tsep_1(X57,X58)
        | v2_struct_0(X59)
        | ~ m1_pre_topc(X59,X56)
        | v2_struct_0(X58)
        | ~ m1_pre_topc(X58,X56)
        | v2_struct_0(X57)
        | ~ m1_pre_topc(X57,X56)
        | v2_struct_0(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tmap_1])])])])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk5_0),X1)
    | r1_tsep_1(esk3_0,esk5_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,k1_tsep_1(esk1_0,esk2_0,esk4_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_16]),c_0_39])]),c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(esk2_0,k1_tsep_1(esk1_0,esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_15]),c_0_18])).

cnf(c_0_47,negated_conjecture,
    ( m1_pre_topc(esk4_0,k1_tsep_1(esk1_0,esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_26]),c_0_15]),c_0_21]),c_0_16]),c_0_39])]),c_0_17]),c_0_22]),c_0_18])).

cnf(c_0_48,plain,
    ( r1_tsep_1(X4,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(k2_tsep_1(X1,X2,X3),X4)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk2_0)
    | r1_tsep_1(esk3_0,esk5_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_15])]),c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk5_0),esk4_0)
    | r1_tsep_1(esk3_0,esk5_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_47]),c_0_21])]),c_0_22])).

cnf(c_0_53,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_54,plain,(
    ! [X39,X40] :
      ( ~ l1_struct_0(X39)
      | ~ l1_struct_0(X40)
      | ~ r1_tsep_1(X39,X40)
      | r1_tsep_1(X40,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_56,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0)
    | r1_tsep_1(esk2_0,esk5_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_15]),c_0_28]),c_0_36]),c_0_16]),c_0_39])]),c_0_17]),c_0_37]),c_0_29]),c_0_18])).

fof(c_0_57,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_pre_topc(X27,X26)
      | l1_pre_topc(X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_21]),c_0_28]),c_0_36]),c_0_16]),c_0_39])]),c_0_17]),c_0_37]),c_0_29]),c_0_22])).

cnf(c_0_59,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk5_0)
    | r1_tsep_1(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_28]),c_0_36]),c_0_16])]),c_0_17]),c_0_37]),c_0_29])).

fof(c_0_61,plain,(
    ! [X25] :
      ( ~ l1_pre_topc(X25)
      | l1_struct_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_62,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_58]),c_0_28]),c_0_36]),c_0_16])]),c_0_17]),c_0_37]),c_0_29])).

cnf(c_0_64,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0)
    | r1_tsep_1(esk5_0,esk2_0)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_28]),c_0_16])])).

cnf(c_0_67,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_36]),c_0_16])])).

cnf(c_0_69,negated_conjecture,
    ( r1_tsep_1(esk5_0,esk2_0)
    | r1_tsep_1(esk3_0,esk5_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])])).

cnf(c_0_70,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_15]),c_0_16])])).

cnf(c_0_71,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(esk3_0,esk5_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_65]),c_0_68])])).

cnf(c_0_72,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_21]),c_0_16])])).

cnf(c_0_73,negated_conjecture,
    ( ~ r1_tsep_1(esk3_0,esk4_0)
    | ~ r1_tsep_1(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_74,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0)
    | r1_tsep_1(esk5_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_65]),c_0_70])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_65]),c_0_72])])).

cnf(c_0_76,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

cnf(c_0_77,negated_conjecture,
    ( r1_tsep_1(esk3_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_76]),c_0_37]),c_0_29])).

fof(c_0_78,plain,(
    ! [X46,X47,X48,X49] :
      ( ( ~ r1_tsep_1(X48,X49)
        | r1_tsep_1(X47,X49)
        | ~ m1_pre_topc(X47,X48)
        | v2_struct_0(X49)
        | ~ m1_pre_topc(X49,X46)
        | v2_struct_0(X48)
        | ~ m1_pre_topc(X48,X46)
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( ~ r1_tsep_1(X49,X48)
        | r1_tsep_1(X47,X49)
        | ~ m1_pre_topc(X47,X48)
        | v2_struct_0(X49)
        | ~ m1_pre_topc(X49,X46)
        | v2_struct_0(X48)
        | ~ m1_pre_topc(X48,X46)
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( ~ r1_tsep_1(X48,X49)
        | r1_tsep_1(X49,X47)
        | ~ m1_pre_topc(X47,X48)
        | v2_struct_0(X49)
        | ~ m1_pre_topc(X49,X46)
        | v2_struct_0(X48)
        | ~ m1_pre_topc(X48,X46)
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( ~ r1_tsep_1(X49,X48)
        | r1_tsep_1(X49,X47)
        | ~ m1_pre_topc(X47,X48)
        | v2_struct_0(X49)
        | ~ m1_pre_topc(X49,X46)
        | v2_struct_0(X48)
        | ~ m1_pre_topc(X48,X46)
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tmap_1])])])])])).

cnf(c_0_79,negated_conjecture,
    ( r1_tsep_1(esk3_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_28]),c_0_36]),c_0_16]),c_0_39])]),c_0_17])).

cnf(c_0_80,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_53]),c_0_21])]),c_0_22])).

cnf(c_0_82,negated_conjecture,
    ( r1_tsep_1(esk5_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_76]),c_0_37]),c_0_29])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tsep_1(esk5_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_81])])).

cnf(c_0_84,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_50]),c_0_83]),c_0_18])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_39]),c_0_28]),c_0_36]),c_0_15]),c_0_16])]),c_0_17]),
    [proof]).
%------------------------------------------------------------------------------
