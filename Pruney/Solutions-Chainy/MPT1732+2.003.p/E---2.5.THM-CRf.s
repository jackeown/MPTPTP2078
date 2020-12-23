%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:11 EST 2020

% Result     : Theorem 1.20s
% Output     : CNFRefutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   56 (1491 expanded)
%              Number of clauses        :   47 ( 460 expanded)
%              Number of leaves         :    4 ( 358 expanded)
%              Depth                    :   23
%              Number of atoms          :  413 (19926 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal clause size      :   48 (   5 average)
%              Maximal term depth       :    2 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tsep_1)).

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

fof(c_0_4,negated_conjecture,(
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

fof(c_0_5,plain,(
    ! [X12,X13,X14] :
      ( ( m1_pre_topc(k2_tsep_1(X12,X13,X14),X13)
        | r1_tsep_1(X13,X14)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_pre_topc(k2_tsep_1(X12,X13,X14),X14)
        | r1_tsep_1(X13,X14)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_tsep_1])])])])])).

fof(c_0_6,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).

fof(c_0_7,plain,(
    ! [X8,X9,X10,X11] :
      ( ( ~ r1_tsep_1(X10,X11)
        | r1_tsep_1(X9,X11)
        | ~ m1_pre_topc(X9,X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X8)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( ~ r1_tsep_1(X11,X10)
        | r1_tsep_1(X9,X11)
        | ~ m1_pre_topc(X9,X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X8)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( ~ r1_tsep_1(X10,X11)
        | r1_tsep_1(X11,X9)
        | ~ m1_pre_topc(X9,X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X8)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( ~ r1_tsep_1(X11,X10)
        | r1_tsep_1(X11,X9)
        | ~ m1_pre_topc(X9,X10)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X8)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tmap_1])])])])])).

cnf(c_0_8,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_14,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v2_struct_0(k2_tsep_1(X5,X6,X7))
        | v2_struct_0(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X5) )
      & ( v1_pre_topc(k2_tsep_1(X5,X6,X7))
        | v2_struct_0(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X5) )
      & ( m1_pre_topc(k2_tsep_1(X5,X6,X7),X5)
        | v2_struct_0(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

cnf(c_0_15,plain,
    ( r1_tsep_1(X3,X2)
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
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])]),c_0_12]),c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(X1,esk4_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_9]),c_0_11])]),c_0_12]),c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_19]),c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_30,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_31,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_10]),c_0_29]),c_0_9]),c_0_11])]),c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_9]),c_0_10]),c_0_11])]),c_0_12]),c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(X1,esk4_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_31]),c_0_17]),c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_25])).

cnf(c_0_36,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_37,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_28]),c_0_10]),c_0_29]),c_0_19]),c_0_11])]),c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(X1,esk4_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_12]),c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_24])).

cnf(c_0_40,plain,
    ( r1_tsep_1(X1,X3)
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
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_42,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_28]),c_0_10]),c_0_9]),c_0_29]),c_0_11])]),c_0_13])).

cnf(c_0_43,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,X1)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_37]),c_0_12]),c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_24]),c_0_44])).

cnf(c_0_46,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_28]),c_0_10]),c_0_9]),c_0_29]),c_0_11])]),c_0_13])).

cnf(c_0_47,negated_conjecture,
    ( r1_tsep_1(X1,esk4_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_46]),c_0_21]),c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_28]),c_0_10]),c_0_19]),c_0_29]),c_0_11])]),c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_46]),c_0_21]),c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_34]),c_0_51])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_54,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_28]),c_0_10]),c_0_19]),c_0_29]),c_0_11])]),c_0_13])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_9]),c_0_19]),c_0_11])]),c_0_12]),c_0_21]),c_0_13]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.20/1.45  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S04CA
% 1.20/1.45  # and selection function MSelectComplexExceptUniqMaxHorn.
% 1.20/1.45  #
% 1.20/1.45  # Preprocessing time       : 0.027 s
% 1.20/1.45  # Presaturation interreduction done
% 1.20/1.45  
% 1.20/1.45  # Proof found!
% 1.20/1.45  # SZS status Theorem
% 1.20/1.45  # SZS output start CNFRefutation
% 1.20/1.45  fof(t41_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X2,X3))=>((~(r1_tsep_1(k2_tsep_1(X1,X2,X3),X4))=>(~(r1_tsep_1(X2,X4))&~(r1_tsep_1(X3,X4))))&(~(r1_tsep_1(X4,k2_tsep_1(X1,X2,X3)))=>(~(r1_tsep_1(X4,X2))&~(r1_tsep_1(X4,X3)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tmap_1)).
% 1.20/1.45  fof(t30_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>(m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)&m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tsep_1)).
% 1.20/1.45  fof(t23_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 1.20/1.45  fof(dt_k2_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k2_tsep_1(X1,X2,X3)))&v1_pre_topc(k2_tsep_1(X1,X2,X3)))&m1_pre_topc(k2_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 1.20/1.45  fof(c_0_4, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X2,X3))=>((~(r1_tsep_1(k2_tsep_1(X1,X2,X3),X4))=>(~(r1_tsep_1(X2,X4))&~(r1_tsep_1(X3,X4))))&(~(r1_tsep_1(X4,k2_tsep_1(X1,X2,X3)))=>(~(r1_tsep_1(X4,X2))&~(r1_tsep_1(X4,X3))))))))))), inference(assume_negation,[status(cth)],[t41_tmap_1])).
% 1.20/1.45  fof(c_0_5, plain, ![X12, X13, X14]:((m1_pre_topc(k2_tsep_1(X12,X13,X14),X13)|r1_tsep_1(X13,X14)|(v2_struct_0(X14)|~m1_pre_topc(X14,X12))|(v2_struct_0(X13)|~m1_pre_topc(X13,X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(m1_pre_topc(k2_tsep_1(X12,X13,X14),X14)|r1_tsep_1(X13,X14)|(v2_struct_0(X14)|~m1_pre_topc(X14,X12))|(v2_struct_0(X13)|~m1_pre_topc(X13,X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_tsep_1])])])])])).
% 1.20/1.45  fof(c_0_6, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(~r1_tsep_1(esk2_0,esk3_0)&(((~r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0))&(r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)))&((~r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk3_0,esk4_0)))&(r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk3_0,esk4_0)))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).
% 1.20/1.45  fof(c_0_7, plain, ![X8, X9, X10, X11]:(((~r1_tsep_1(X10,X11)|r1_tsep_1(X9,X11)|~m1_pre_topc(X9,X10)|(v2_struct_0(X11)|~m1_pre_topc(X11,X8))|(v2_struct_0(X10)|~m1_pre_topc(X10,X8))|(v2_struct_0(X9)|~m1_pre_topc(X9,X8))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)))&(~r1_tsep_1(X11,X10)|r1_tsep_1(X9,X11)|~m1_pre_topc(X9,X10)|(v2_struct_0(X11)|~m1_pre_topc(X11,X8))|(v2_struct_0(X10)|~m1_pre_topc(X10,X8))|(v2_struct_0(X9)|~m1_pre_topc(X9,X8))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8))))&((~r1_tsep_1(X10,X11)|r1_tsep_1(X11,X9)|~m1_pre_topc(X9,X10)|(v2_struct_0(X11)|~m1_pre_topc(X11,X8))|(v2_struct_0(X10)|~m1_pre_topc(X10,X8))|(v2_struct_0(X9)|~m1_pre_topc(X9,X8))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)))&(~r1_tsep_1(X11,X10)|r1_tsep_1(X11,X9)|~m1_pre_topc(X9,X10)|(v2_struct_0(X11)|~m1_pre_topc(X11,X8))|(v2_struct_0(X10)|~m1_pre_topc(X10,X8))|(v2_struct_0(X9)|~m1_pre_topc(X9,X8))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_tmap_1])])])])])).
% 1.20/1.45  cnf(c_0_8, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 1.20/1.45  cnf(c_0_9, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.20/1.45  cnf(c_0_10, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.20/1.45  cnf(c_0_11, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.20/1.45  cnf(c_0_12, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.20/1.45  cnf(c_0_13, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.20/1.45  fof(c_0_14, plain, ![X5, X6, X7]:(((~v2_struct_0(k2_tsep_1(X5,X6,X7))|(v2_struct_0(X5)|~l1_pre_topc(X5)|v2_struct_0(X6)|~m1_pre_topc(X6,X5)|v2_struct_0(X7)|~m1_pre_topc(X7,X5)))&(v1_pre_topc(k2_tsep_1(X5,X6,X7))|(v2_struct_0(X5)|~l1_pre_topc(X5)|v2_struct_0(X6)|~m1_pre_topc(X6,X5)|v2_struct_0(X7)|~m1_pre_topc(X7,X5))))&(m1_pre_topc(k2_tsep_1(X5,X6,X7),X5)|(v2_struct_0(X5)|~l1_pre_topc(X5)|v2_struct_0(X6)|~m1_pre_topc(X6,X5)|v2_struct_0(X7)|~m1_pre_topc(X7,X5)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).
% 1.20/1.45  cnf(c_0_15, plain, (r1_tsep_1(X3,X2)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X4)|~r1_tsep_1(X1,X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X4)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X3,X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.20/1.45  cnf(c_0_16, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.20/1.45  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.20/1.45  cnf(c_0_18, negated_conjecture, (r1_tsep_1(X1,esk3_0)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk3_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), c_0_11])]), c_0_12]), c_0_13])).
% 1.20/1.45  cnf(c_0_19, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.20/1.45  cnf(c_0_20, negated_conjecture, (~r1_tsep_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.20/1.45  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.20/1.45  cnf(c_0_22, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.20/1.45  cnf(c_0_23, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(X1,esk4_0)|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X2)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(esk4_0,X2)|~m1_pre_topc(esk3_0,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_12])).
% 1.20/1.45  cnf(c_0_24, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])).
% 1.20/1.45  cnf(c_0_25, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.20/1.45  cnf(c_0_26, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk1_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_9]), c_0_11])]), c_0_12]), c_0_13])).
% 1.20/1.45  cnf(c_0_27, negated_conjecture, (r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 1.20/1.45  cnf(c_0_28, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_19]), c_0_21])).
% 1.20/1.45  cnf(c_0_29, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.20/1.45  cnf(c_0_30, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 1.20/1.45  cnf(c_0_31, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk2_0,esk4_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_10]), c_0_29]), c_0_9]), c_0_11])]), c_0_13])).
% 1.20/1.45  cnf(c_0_32, negated_conjecture, (r1_tsep_1(X1,esk3_0)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),X1)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_9]), c_0_10]), c_0_11])]), c_0_12]), c_0_13])).
% 1.20/1.45  cnf(c_0_33, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(X1,esk4_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X2)|~m1_pre_topc(X1,esk2_0)|~m1_pre_topc(esk4_0,X2)|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_31]), c_0_17]), c_0_21])).
% 1.20/1.45  cnf(c_0_34, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_19]), c_0_20]), c_0_21])).
% 1.20/1.45  cnf(c_0_35, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk4_0,esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_25])).
% 1.20/1.45  cnf(c_0_36, plain, (r1_tsep_1(X3,X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~r1_tsep_1(X1,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X2,X4)|~m1_pre_topc(X3,X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.20/1.45  cnf(c_0_37, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_28]), c_0_10]), c_0_29]), c_0_19]), c_0_11])]), c_0_13])).
% 1.20/1.45  cnf(c_0_38, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(X1,esk4_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X2)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(esk3_0,X2)|~m1_pre_topc(esk4_0,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_12]), c_0_17])).
% 1.20/1.45  cnf(c_0_39, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|r1_tsep_1(esk4_0,esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_24])).
% 1.20/1.45  cnf(c_0_40, plain, (r1_tsep_1(X1,X3)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~r1_tsep_1(X1,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X2,X4)|~m1_pre_topc(X3,X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.20/1.45  cnf(c_0_41, negated_conjecture, (~r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.20/1.45  cnf(c_0_42, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|r1_tsep_1(esk4_0,esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_28]), c_0_10]), c_0_9]), c_0_29]), c_0_11])]), c_0_13])).
% 1.20/1.45  cnf(c_0_43, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,X1)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X2)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(esk3_0,X2)|~m1_pre_topc(esk4_0,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_37]), c_0_12]), c_0_17])).
% 1.20/1.45  cnf(c_0_44, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.20/1.45  cnf(c_0_45, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_24]), c_0_44])).
% 1.20/1.45  cnf(c_0_46, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_28]), c_0_10]), c_0_9]), c_0_29]), c_0_11])]), c_0_13])).
% 1.20/1.45  cnf(c_0_47, negated_conjecture, (r1_tsep_1(X1,esk4_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X2)|~m1_pre_topc(X1,esk2_0)|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(esk4_0,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_46]), c_0_21]), c_0_17])).
% 1.20/1.45  cnf(c_0_48, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_47, c_0_34])).
% 1.20/1.45  cnf(c_0_49, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_28]), c_0_10]), c_0_19]), c_0_29]), c_0_11])]), c_0_13])).
% 1.20/1.45  cnf(c_0_50, negated_conjecture, (r1_tsep_1(esk4_0,X1)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X2)|~m1_pre_topc(X1,esk2_0)|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(esk4_0,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_46]), c_0_21]), c_0_17])).
% 1.20/1.45  cnf(c_0_51, negated_conjecture, (v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_41, c_0_49])).
% 1.20/1.45  cnf(c_0_52, negated_conjecture, (v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_34]), c_0_51])).
% 1.20/1.45  cnf(c_0_53, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k2_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.20/1.45  cnf(c_0_54, negated_conjecture, (v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_28]), c_0_10]), c_0_19]), c_0_29]), c_0_11])]), c_0_13])).
% 1.20/1.45  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_9]), c_0_19]), c_0_11])]), c_0_12]), c_0_21]), c_0_13]), ['proof']).
% 1.20/1.45  # SZS output end CNFRefutation
% 1.20/1.45  # Proof object total steps             : 56
% 1.20/1.45  # Proof object clause steps            : 47
% 1.20/1.45  # Proof object formula steps           : 9
% 1.20/1.45  # Proof object conjectures             : 43
% 1.20/1.45  # Proof object clause conjectures      : 40
% 1.20/1.45  # Proof object formula conjectures     : 3
% 1.20/1.45  # Proof object initial clauses used    : 20
% 1.20/1.45  # Proof object initial formulas used   : 4
% 1.20/1.45  # Proof object generating inferences   : 27
% 1.20/1.45  # Proof object simplifying inferences  : 78
% 1.20/1.45  # Training examples: 0 positive, 0 negative
% 1.20/1.45  # Parsed axioms                        : 4
% 1.20/1.45  # Removed by relevancy pruning/SinE    : 0
% 1.20/1.45  # Initial clauses                      : 23
% 1.20/1.45  # Removed in clause preprocessing      : 0
% 1.20/1.45  # Initial clauses in saturation        : 23
% 1.20/1.45  # Processed clauses                    : 1868
% 1.20/1.45  # ...of these trivial                  : 0
% 1.20/1.45  # ...subsumed                          : 64
% 1.20/1.45  # ...remaining for further processing  : 1804
% 1.20/1.45  # Other redundant clauses eliminated   : 0
% 1.20/1.45  # Clauses deleted for lack of memory   : 0
% 1.20/1.45  # Backward-subsumed                    : 97
% 1.20/1.45  # Backward-rewritten                   : 325
% 1.20/1.45  # Generated clauses                    : 121609
% 1.20/1.45  # ...of the previous two non-trivial   : 121608
% 1.20/1.45  # Contextual simplify-reflections      : 12
% 1.20/1.45  # Paramodulations                      : 121609
% 1.20/1.45  # Factorizations                       : 0
% 1.20/1.45  # Equation resolutions                 : 0
% 1.20/1.45  # Propositional unsat checks           : 0
% 1.20/1.45  #    Propositional check models        : 0
% 1.20/1.45  #    Propositional check unsatisfiable : 0
% 1.20/1.45  #    Propositional clauses             : 0
% 1.20/1.45  #    Propositional clauses after purity: 0
% 1.20/1.45  #    Propositional unsat core size     : 0
% 1.20/1.45  #    Propositional preprocessing time  : 0.000
% 1.20/1.45  #    Propositional encoding time       : 0.000
% 1.20/1.45  #    Propositional solver time         : 0.000
% 1.20/1.45  #    Success case prop preproc time    : 0.000
% 1.20/1.45  #    Success case prop encoding time   : 0.000
% 1.20/1.45  #    Success case prop solver time     : 0.000
% 1.20/1.45  # Current number of processed clauses  : 1359
% 1.20/1.45  #    Positive orientable unit clauses  : 26
% 1.20/1.45  #    Positive unorientable unit clauses: 0
% 1.20/1.45  #    Negative unit clauses             : 5
% 1.20/1.45  #    Non-unit-clauses                  : 1328
% 1.20/1.45  # Current number of unprocessed clauses: 119672
% 1.20/1.45  # ...number of literals in the above   : 704525
% 1.20/1.45  # Current number of archived formulas  : 0
% 1.20/1.45  # Current number of archived clauses   : 445
% 1.20/1.45  # Clause-clause subsumption calls (NU) : 270702
% 1.20/1.45  # Rec. Clause-clause subsumption calls : 37712
% 1.20/1.45  # Non-unit clause-clause subsumptions  : 173
% 1.20/1.45  # Unit Clause-clause subsumption calls : 663
% 1.20/1.45  # Rewrite failures with RHS unbound    : 0
% 1.20/1.45  # BW rewrite match attempts            : 31
% 1.20/1.45  # BW rewrite match successes           : 1
% 1.20/1.45  # Condensation attempts                : 0
% 1.20/1.45  # Condensation successes               : 0
% 1.20/1.45  # Termbank termtop insertions          : 6858126
% 1.30/1.46  
% 1.30/1.46  # -------------------------------------------------
% 1.30/1.46  # User time                : 1.035 s
% 1.30/1.46  # System time              : 0.084 s
% 1.30/1.46  # Total time               : 1.119 s
% 1.30/1.46  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
