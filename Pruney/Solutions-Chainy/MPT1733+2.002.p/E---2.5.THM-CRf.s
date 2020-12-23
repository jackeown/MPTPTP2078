%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:12 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   52 (1916 expanded)
%              Number of clauses        :   47 ( 583 expanded)
%              Number of leaves         :    2 ( 457 expanded)
%              Depth                    :   31
%              Number of atoms          :  336 (26739 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   48 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_tmap_1,conjecture,(
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
                   => ( ( ( r1_tsep_1(X2,X4)
                          | r1_tsep_1(X3,X4) )
                       => r1_tsep_1(k2_tsep_1(X1,X2,X3),X4) )
                      & ( ( r1_tsep_1(X4,X2)
                          | r1_tsep_1(X4,X3) )
                       => r1_tsep_1(X4,k2_tsep_1(X1,X2,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tmap_1)).

fof(t41_tmap_1,axiom,(
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

fof(c_0_2,negated_conjecture,(
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
                     => ( ( ( r1_tsep_1(X2,X4)
                            | r1_tsep_1(X3,X4) )
                         => r1_tsep_1(k2_tsep_1(X1,X2,X3),X4) )
                        & ( ( r1_tsep_1(X4,X2)
                            | r1_tsep_1(X4,X3) )
                         => r1_tsep_1(X4,k2_tsep_1(X1,X2,X3)) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t42_tmap_1])).

fof(c_0_3,plain,(
    ! [X5,X6,X7,X8] :
      ( ( ~ r1_tsep_1(X6,X8)
        | r1_tsep_1(k2_tsep_1(X5,X6,X7),X8)
        | r1_tsep_1(X6,X7)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,X5)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( ~ r1_tsep_1(X7,X8)
        | r1_tsep_1(k2_tsep_1(X5,X6,X7),X8)
        | r1_tsep_1(X6,X7)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,X5)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( ~ r1_tsep_1(X8,X6)
        | r1_tsep_1(X8,k2_tsep_1(X5,X6,X7))
        | r1_tsep_1(X6,X7)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,X5)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( ~ r1_tsep_1(X8,X7)
        | r1_tsep_1(X8,k2_tsep_1(X5,X6,X7))
        | r1_tsep_1(X6,X7)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,X5)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_tmap_1])])])])])).

fof(c_0_4,negated_conjecture,
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
    & ( r1_tsep_1(esk4_0,esk2_0)
      | r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk2_0,esk4_0)
      | r1_tsep_1(esk3_0,esk4_0) )
    & ( ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk2_0,esk4_0)
      | r1_tsep_1(esk3_0,esk4_0) )
    & ( r1_tsep_1(esk4_0,esk2_0)
      | r1_tsep_1(esk4_0,esk3_0)
      | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])])).

cnf(c_0_5,plain,
    ( r1_tsep_1(k2_tsep_1(X3,X4,X1),X2)
    | r1_tsep_1(X4,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(X1,X2,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(X2,esk3_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7]),c_0_8])).

cnf(c_0_10,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,X1,esk3_0),esk4_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_16,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,plain,
    ( r1_tsep_1(k2_tsep_1(X3,X1,X4),X2)
    | r1_tsep_1(X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_21,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(X1,esk2_0,X2),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk2_0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_7]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,X1),esk4_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_10]),c_0_16]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_24,plain,
    ( r1_tsep_1(X1,k2_tsep_1(X3,X4,X2))
    | r1_tsep_1(X4,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_25,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_11]),c_0_17]),c_0_8]),c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r1_tsep_1(esk4_0,k2_tsep_1(X1,X2,esk3_0))
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(X2,esk3_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_8]),c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,X1,esk3_0))
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_11]),c_0_10]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_29,negated_conjecture,
    ( r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_31,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(X1,X2,esk3_0),esk4_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(X2,esk3_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_30]),c_0_7]),c_0_8])).

cnf(c_0_32,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,X1,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_34,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(X1,esk2_0,X2),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_35]),c_0_7]),c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,X1),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_10]),c_0_16]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_11]),c_0_17]),c_0_8])).

cnf(c_0_39,plain,
    ( r1_tsep_1(X1,k2_tsep_1(X3,X2,X4))
    | r1_tsep_1(X2,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_40,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_38]),c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( r1_tsep_1(esk4_0,k2_tsep_1(X1,esk2_0,X2))
    | r1_tsep_1(esk2_0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_18]),c_0_7])).

cnf(c_0_42,negated_conjecture,
    ( r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,X1))
    | r1_tsep_1(esk2_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_16]),c_0_10]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_11]),c_0_17]),c_0_8])).

cnf(c_0_44,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_43])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(X1,X2,esk3_0),esk4_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(X2,esk3_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_44]),c_0_7]),c_0_8])).

cnf(c_0_46,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,X1,esk3_0),esk4_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_43])])).

cnf(c_0_48,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_16]),c_0_47]),c_0_17]),c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(X1,esk2_0,X2),esk4_0)
    | r1_tsep_1(esk2_0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_48]),c_0_7]),c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,X1),esk4_0)
    | r1_tsep_1(esk2_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_10]),c_0_16]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_11]),c_0_47]),c_0_17]),c_0_8]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:50:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S04CA
% 0.12/0.38  # and selection function MSelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.027 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t42_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X2,X3))=>(((r1_tsep_1(X2,X4)|r1_tsep_1(X3,X4))=>r1_tsep_1(k2_tsep_1(X1,X2,X3),X4))&((r1_tsep_1(X4,X2)|r1_tsep_1(X4,X3))=>r1_tsep_1(X4,k2_tsep_1(X1,X2,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tmap_1)).
% 0.12/0.38  fof(t41_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X2,X3))=>((~(r1_tsep_1(k2_tsep_1(X1,X2,X3),X4))=>(~(r1_tsep_1(X2,X4))&~(r1_tsep_1(X3,X4))))&(~(r1_tsep_1(X4,k2_tsep_1(X1,X2,X3)))=>(~(r1_tsep_1(X4,X2))&~(r1_tsep_1(X4,X3)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tmap_1)).
% 0.12/0.38  fof(c_0_2, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X2,X3))=>(((r1_tsep_1(X2,X4)|r1_tsep_1(X3,X4))=>r1_tsep_1(k2_tsep_1(X1,X2,X3),X4))&((r1_tsep_1(X4,X2)|r1_tsep_1(X4,X3))=>r1_tsep_1(X4,k2_tsep_1(X1,X2,X3)))))))))), inference(assume_negation,[status(cth)],[t42_tmap_1])).
% 0.12/0.38  fof(c_0_3, plain, ![X5, X6, X7, X8]:(((~r1_tsep_1(X6,X8)|r1_tsep_1(k2_tsep_1(X5,X6,X7),X8)|r1_tsep_1(X6,X7)|(v2_struct_0(X8)|~m1_pre_topc(X8,X5))|(v2_struct_0(X7)|~m1_pre_topc(X7,X5))|(v2_struct_0(X6)|~m1_pre_topc(X6,X5))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5)))&(~r1_tsep_1(X7,X8)|r1_tsep_1(k2_tsep_1(X5,X6,X7),X8)|r1_tsep_1(X6,X7)|(v2_struct_0(X8)|~m1_pre_topc(X8,X5))|(v2_struct_0(X7)|~m1_pre_topc(X7,X5))|(v2_struct_0(X6)|~m1_pre_topc(X6,X5))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))&((~r1_tsep_1(X8,X6)|r1_tsep_1(X8,k2_tsep_1(X5,X6,X7))|r1_tsep_1(X6,X7)|(v2_struct_0(X8)|~m1_pre_topc(X8,X5))|(v2_struct_0(X7)|~m1_pre_topc(X7,X5))|(v2_struct_0(X6)|~m1_pre_topc(X6,X5))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5)))&(~r1_tsep_1(X8,X7)|r1_tsep_1(X8,k2_tsep_1(X5,X6,X7))|r1_tsep_1(X6,X7)|(v2_struct_0(X8)|~m1_pre_topc(X8,X5))|(v2_struct_0(X7)|~m1_pre_topc(X7,X5))|(v2_struct_0(X6)|~m1_pre_topc(X6,X5))|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_tmap_1])])])])])).
% 0.12/0.38  fof(c_0_4, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(~r1_tsep_1(esk2_0,esk3_0)&(((r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk3_0,esk4_0)))&(~r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk3_0,esk4_0))))&((r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0))&(~r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])])).
% 0.12/0.38  cnf(c_0_5, plain, (r1_tsep_1(k2_tsep_1(X3,X4,X1),X2)|r1_tsep_1(X4,X1)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X3)|~r1_tsep_1(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X4,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.38  cnf(c_0_6, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_7, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_8, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_9, negated_conjecture, (r1_tsep_1(k2_tsep_1(X1,X2,esk3_0),esk4_0)|r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(X2,esk3_0)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_6]), c_0_7]), c_0_8])).
% 0.12/0.38  cnf(c_0_10, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_11, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_12, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_13, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_14, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_15, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,X1,esk3_0),esk4_0)|r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.12/0.38  cnf(c_0_16, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_17, negated_conjecture, (~r1_tsep_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_20, plain, (r1_tsep_1(k2_tsep_1(X3,X1,X4),X2)|r1_tsep_1(X1,X4)|v2_struct_0(X2)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X3)|~r1_tsep_1(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.38  cnf(c_0_21, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk2_0,esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19])).
% 0.12/0.38  cnf(c_0_22, negated_conjecture, (r1_tsep_1(k2_tsep_1(X1,esk2_0,X2),esk4_0)|r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk2_0,X2)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_7]), c_0_18])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,X1),esk4_0)|r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk2_0,X1)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_10]), c_0_16]), c_0_12]), c_0_13])]), c_0_14])).
% 0.12/0.38  cnf(c_0_24, plain, (r1_tsep_1(X1,k2_tsep_1(X3,X4,X2))|r1_tsep_1(X4,X2)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X4)|v2_struct_0(X3)|~r1_tsep_1(X1,X2)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X4,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_11]), c_0_17]), c_0_8]), c_0_19])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (r1_tsep_1(esk4_0,k2_tsep_1(X1,X2,esk3_0))|r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(X2,esk3_0)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_8]), c_0_7])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,X1,esk3_0))|r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_11]), c_0_10]), c_0_12]), c_0_13])]), c_0_14])).
% 0.12/0.38  cnf(c_0_28, negated_conjecture, (r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk3_0,esk4_0)|~r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_16]), c_0_17]), c_0_18])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (r1_tsep_1(k2_tsep_1(X1,X2,esk3_0),esk4_0)|r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(X2,esk3_0)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_30]), c_0_7]), c_0_8])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,X1,esk3_0),esk4_0)|r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (~r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_16]), c_0_17]), c_0_18])).
% 0.12/0.38  cnf(c_0_35, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk2_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_29])).
% 0.12/0.38  cnf(c_0_36, negated_conjecture, (r1_tsep_1(k2_tsep_1(X1,esk2_0,X2),esk4_0)|r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk2_0,X2)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_35]), c_0_7]), c_0_18])).
% 0.12/0.38  cnf(c_0_37, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,X1),esk4_0)|r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk2_0,X1)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_10]), c_0_16]), c_0_12]), c_0_13])]), c_0_14])).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|r1_tsep_1(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_11]), c_0_17]), c_0_8])).
% 0.12/0.38  cnf(c_0_39, plain, (r1_tsep_1(X1,k2_tsep_1(X3,X2,X4))|r1_tsep_1(X2,X4)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tsep_1(X1,X2)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X2,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_38]), c_0_29])).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, (r1_tsep_1(esk4_0,k2_tsep_1(X1,esk2_0,X2))|r1_tsep_1(esk2_0,X2)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_18]), c_0_7])).
% 0.12/0.38  cnf(c_0_42, negated_conjecture, (r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,X1))|r1_tsep_1(esk2_0,X1)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_16]), c_0_10]), c_0_12]), c_0_13])]), c_0_14])).
% 0.12/0.38  cnf(c_0_43, negated_conjecture, (r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_11]), c_0_17]), c_0_8])).
% 0.12/0.38  cnf(c_0_44, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)|r1_tsep_1(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_43])])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (r1_tsep_1(k2_tsep_1(X1,X2,esk3_0),esk4_0)|r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(X2,esk3_0)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_44]), c_0_7]), c_0_8])).
% 0.12/0.38  cnf(c_0_46, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,X1,esk3_0),esk4_0)|r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.12/0.38  cnf(c_0_47, negated_conjecture, (~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_43])])).
% 0.12/0.38  cnf(c_0_48, negated_conjecture, (r1_tsep_1(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_16]), c_0_47]), c_0_17]), c_0_18])).
% 0.12/0.38  cnf(c_0_49, negated_conjecture, (r1_tsep_1(k2_tsep_1(X1,esk2_0,X2),esk4_0)|r1_tsep_1(esk2_0,X2)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_48]), c_0_7]), c_0_18])).
% 0.12/0.38  cnf(c_0_50, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,X1),esk4_0)|r1_tsep_1(esk2_0,X1)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_10]), c_0_16]), c_0_12]), c_0_13])]), c_0_14])).
% 0.12/0.38  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_11]), c_0_47]), c_0_17]), c_0_8]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 52
% 0.12/0.38  # Proof object clause steps            : 47
% 0.12/0.38  # Proof object formula steps           : 5
% 0.12/0.38  # Proof object conjectures             : 46
% 0.12/0.38  # Proof object clause conjectures      : 43
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 18
% 0.12/0.38  # Proof object initial formulas used   : 2
% 0.12/0.38  # Proof object generating inferences   : 27
% 0.12/0.38  # Proof object simplifying inferences  : 82
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 2
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 18
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 18
% 0.12/0.38  # Processed clauses                    : 121
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 10
% 0.12/0.38  # ...remaining for further processing  : 111
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 26
% 0.12/0.38  # Backward-rewritten                   : 33
% 0.12/0.38  # Generated clauses                    : 215
% 0.12/0.38  # ...of the previous two non-trivial   : 212
% 0.12/0.38  # Contextual simplify-reflections      : 4
% 0.12/0.38  # Paramodulations                      : 215
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 34
% 0.12/0.38  #    Positive orientable unit clauses  : 8
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 6
% 0.12/0.38  #    Non-unit-clauses                  : 20
% 0.12/0.38  # Current number of unprocessed clauses: 44
% 0.12/0.38  # ...number of literals in the above   : 480
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 77
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 814
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 97
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 40
% 0.12/0.38  # Unit Clause-clause subsumption calls : 17
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 4
% 0.12/0.38  # BW rewrite match successes           : 3
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 10400
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.035 s
% 0.12/0.38  # System time              : 0.007 s
% 0.12/0.38  # Total time               : 0.043 s
% 0.12/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
