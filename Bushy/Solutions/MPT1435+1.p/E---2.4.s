%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : filter_1__t30_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:08 EDT 2019

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   88 (3537 expanded)
%              Number of clauses        :   77 (1096 expanded)
%              Number of leaves         :    5 ( 852 expanded)
%              Depth                    :   17
%              Number of atoms          :  562 (46981 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   49 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t30_filter_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) )
                         => ( ( r6_binop_1(X1,X3,X4)
                              & r6_binop_1(X2,X5,X6) )
                          <=> r6_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X5),k6_filter_1(X1,X2,X4,X6)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t30_filter_1.p',t30_filter_1)).

fof(dt_k6_filter_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) )
     => ( v1_funct_1(k6_filter_1(X1,X2,X3,X4))
        & v1_funct_2(k6_filter_1(X1,X2,X3,X4),k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))
        & m1_subset_1(k6_filter_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t30_filter_1.p',dt_k6_filter_1)).

fof(d11_binop_1,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
         => ( r6_binop_1(X1,X2,X3)
          <=> ( r4_binop_1(X1,X2,X3)
              & r5_binop_1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t30_filter_1.p',d11_binop_1)).

fof(t29_filter_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) )
                         => ( ( r5_binop_1(X1,X3,X4)
                              & r5_binop_1(X2,X5,X6) )
                          <=> r5_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X5),k6_filter_1(X1,X2,X4,X6)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t30_filter_1.p',t29_filter_1)).

fof(t28_filter_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) )
                         => ( ( r4_binop_1(X1,X3,X4)
                              & r4_binop_1(X2,X5,X6) )
                          <=> r4_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X5),k6_filter_1(X1,X2,X4,X6)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t30_filter_1.p',t28_filter_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) )
                           => ( ( r6_binop_1(X1,X3,X4)
                                & r6_binop_1(X2,X5,X6) )
                            <=> r6_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X5),k6_filter_1(X1,X2,X4,X6)) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t30_filter_1])).

fof(c_0_6,plain,(
    ! [X20,X21,X22,X23] :
      ( ( v1_funct_1(k6_filter_1(X20,X21,X22,X23))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,k2_zfmisc_1(X20,X20),X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X20),X20)))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,k2_zfmisc_1(X21,X21),X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X21,X21),X21))) )
      & ( v1_funct_2(k6_filter_1(X20,X21,X22,X23),k2_zfmisc_1(k2_zfmisc_1(X20,X21),k2_zfmisc_1(X20,X21)),k2_zfmisc_1(X20,X21))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,k2_zfmisc_1(X20,X20),X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X20),X20)))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,k2_zfmisc_1(X21,X21),X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X21,X21),X21))) )
      & ( m1_subset_1(k6_filter_1(X20,X21,X22,X23),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X21),k2_zfmisc_1(X20,X21)),k2_zfmisc_1(X20,X21))))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,k2_zfmisc_1(X20,X20),X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X20),X20)))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,k2_zfmisc_1(X21,X21),X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X21,X21),X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_filter_1])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))
    & ( ~ r6_binop_1(esk1_0,esk3_0,esk4_0)
      | ~ r6_binop_1(esk2_0,esk5_0,esk6_0)
      | ~ r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0)) )
    & ( r6_binop_1(esk1_0,esk3_0,esk4_0)
      | r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0)) )
    & ( r6_binop_1(esk2_0,esk5_0,esk6_0)
      | r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).

cnf(c_0_8,plain,
    ( v1_funct_1(k6_filter_1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_2(esk6_0,k2_zfmisc_1(esk2_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_2(esk5_0,k2_zfmisc_1(esk2_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_15,plain,(
    ! [X15,X16,X17] :
      ( ( r4_binop_1(X15,X16,X17)
        | ~ r6_binop_1(X15,X16,X17)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15))) )
      & ( r5_binop_1(X15,X16,X17)
        | ~ r6_binop_1(X15,X16,X17)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15))) )
      & ( ~ r4_binop_1(X15,X16,X17)
        | ~ r5_binop_1(X15,X16,X17)
        | r6_binop_1(X15,X16,X17)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_binop_1])])])])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(k6_filter_1(X1,esk2_0,X2,esk6_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_2(esk4_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(k6_filter_1(X1,esk2_0,X2,esk5_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_2(esk3_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,plain,
    ( v1_funct_2(k6_filter_1(X1,X2,X3,X4),k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,plain,
    ( r5_binop_1(X1,X2,X3)
    | ~ r6_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( r6_binop_1(esk2_0,esk5_0,esk6_0)
    | r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(k6_filter_1(X1,esk2_0,X2,esk6_0),k2_zfmisc_1(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(X1,esk2_0)),k2_zfmisc_1(X1,esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_30,negated_conjecture,
    ( r5_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk2_0,esk5_0,esk6_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(k6_filter_1(X1,esk2_0,X2,esk5_0),k2_zfmisc_1(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(X1,esk2_0)),k2_zfmisc_1(X1,esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_33,plain,
    ( m1_subset_1(k6_filter_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_34,plain,
    ( r4_binop_1(X1,X2,X3)
    | ~ r6_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( r5_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk2_0,esk5_0,esk6_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k6_filter_1(X1,esk2_0,X2,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(X1,esk2_0)),k2_zfmisc_1(X1,esk2_0))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_38,negated_conjecture,
    ( r6_binop_1(esk1_0,esk3_0,esk4_0)
    | r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_39,negated_conjecture,
    ( r4_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk2_0,esk5_0,esk6_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_40,negated_conjecture,
    ( r5_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk2_0,esk5_0,esk6_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k6_filter_1(X1,esk2_0,X2,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(X1,esk2_0)),k2_zfmisc_1(X1,esk2_0))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_43,negated_conjecture,
    ( r5_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_38]),c_0_27]),c_0_28])])).

cnf(c_0_44,negated_conjecture,
    ( r4_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_38]),c_0_27]),c_0_28])])).

cnf(c_0_45,negated_conjecture,
    ( r4_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk2_0,esk5_0,esk6_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_31])])).

fof(c_0_46,plain,(
    ! [X41,X42,X43,X44,X45,X46] :
      ( ( ~ r5_binop_1(X41,X43,X44)
        | ~ r5_binop_1(X42,X45,X46)
        | r5_binop_1(k2_zfmisc_1(X41,X42),k6_filter_1(X41,X42,X43,X45),k6_filter_1(X41,X42,X44,X46))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,k2_zfmisc_1(X42,X42),X42)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X42,X42),X42)))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,k2_zfmisc_1(X42,X42),X42)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X42,X42),X42)))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,k2_zfmisc_1(X41,X41),X41)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X41,X41),X41)))
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,k2_zfmisc_1(X41,X41),X41)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X41,X41),X41)))
        | v1_xboole_0(X42)
        | v1_xboole_0(X41) )
      & ( r5_binop_1(X41,X43,X44)
        | ~ r5_binop_1(k2_zfmisc_1(X41,X42),k6_filter_1(X41,X42,X43,X45),k6_filter_1(X41,X42,X44,X46))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,k2_zfmisc_1(X42,X42),X42)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X42,X42),X42)))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,k2_zfmisc_1(X42,X42),X42)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X42,X42),X42)))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,k2_zfmisc_1(X41,X41),X41)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X41,X41),X41)))
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,k2_zfmisc_1(X41,X41),X41)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X41,X41),X41)))
        | v1_xboole_0(X42)
        | v1_xboole_0(X41) )
      & ( r5_binop_1(X42,X45,X46)
        | ~ r5_binop_1(k2_zfmisc_1(X41,X42),k6_filter_1(X41,X42,X43,X45),k6_filter_1(X41,X42,X44,X46))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,k2_zfmisc_1(X42,X42),X42)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X42,X42),X42)))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,k2_zfmisc_1(X42,X42),X42)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X42,X42),X42)))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,k2_zfmisc_1(X41,X41),X41)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X41,X41),X41)))
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,k2_zfmisc_1(X41,X41),X41)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X41,X41),X41)))
        | v1_xboole_0(X42)
        | v1_xboole_0(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_filter_1])])])])])).

cnf(c_0_47,negated_conjecture,
    ( r5_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk2_0,esk5_0,esk6_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_49,negated_conjecture,
    ( r5_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_31])])).

cnf(c_0_50,negated_conjecture,
    ( r4_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_31])])).

cnf(c_0_51,negated_conjecture,
    ( r4_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk2_0,esk5_0,esk6_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_36])])).

cnf(c_0_52,plain,
    ( r5_binop_1(X1,X2,X3)
    | v1_xboole_0(X1)
    | v1_xboole_0(X4)
    | ~ r5_binop_1(k2_zfmisc_1(X4,X1),k6_filter_1(X4,X1,X5,X2),k6_filter_1(X4,X1,X6,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r5_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk2_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_56,negated_conjecture,
    ( r5_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_36])])).

cnf(c_0_57,negated_conjecture,
    ( r4_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_36])])).

fof(c_0_58,plain,(
    ! [X35,X36,X37,X38,X39,X40] :
      ( ( ~ r4_binop_1(X35,X37,X38)
        | ~ r4_binop_1(X36,X39,X40)
        | r4_binop_1(k2_zfmisc_1(X35,X36),k6_filter_1(X35,X36,X37,X39),k6_filter_1(X35,X36,X38,X40))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,k2_zfmisc_1(X36,X36),X36)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X36,X36),X36)))
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,k2_zfmisc_1(X36,X36),X36)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X36,X36),X36)))
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,k2_zfmisc_1(X35,X35),X35)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X35,X35),X35)))
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,k2_zfmisc_1(X35,X35),X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X35,X35),X35)))
        | v1_xboole_0(X36)
        | v1_xboole_0(X35) )
      & ( r4_binop_1(X35,X37,X38)
        | ~ r4_binop_1(k2_zfmisc_1(X35,X36),k6_filter_1(X35,X36,X37,X39),k6_filter_1(X35,X36,X38,X40))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,k2_zfmisc_1(X36,X36),X36)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X36,X36),X36)))
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,k2_zfmisc_1(X36,X36),X36)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X36,X36),X36)))
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,k2_zfmisc_1(X35,X35),X35)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X35,X35),X35)))
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,k2_zfmisc_1(X35,X35),X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X35,X35),X35)))
        | v1_xboole_0(X36)
        | v1_xboole_0(X35) )
      & ( r4_binop_1(X36,X39,X40)
        | ~ r4_binop_1(k2_zfmisc_1(X35,X36),k6_filter_1(X35,X36,X37,X39),k6_filter_1(X35,X36,X38,X40))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,k2_zfmisc_1(X36,X36),X36)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X36,X36),X36)))
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,k2_zfmisc_1(X36,X36),X36)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X36,X36),X36)))
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,k2_zfmisc_1(X35,X35),X35)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X35,X35),X35)))
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,k2_zfmisc_1(X35,X35),X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X35,X35),X35)))
        | v1_xboole_0(X36)
        | v1_xboole_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t28_filter_1])])])])])).

cnf(c_0_59,negated_conjecture,
    ( r4_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk2_0,esk5_0,esk6_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_41])])).

cnf(c_0_60,plain,
    ( r6_binop_1(X1,X2,X3)
    | ~ r4_binop_1(X1,X2,X3)
    | ~ r5_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_61,negated_conjecture,
    ( r5_binop_1(esk2_0,esk5_0,esk6_0)
    | r6_binop_1(esk2_0,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_18]),c_0_22]),c_0_10]),c_0_13]),c_0_17]),c_0_21]),c_0_9]),c_0_12]),c_0_19]),c_0_23]),c_0_11]),c_0_14])]),c_0_54]),c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( r5_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_41])])).

cnf(c_0_63,negated_conjecture,
    ( r4_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_41])])).

cnf(c_0_64,plain,
    ( r4_binop_1(X1,X2,X3)
    | v1_xboole_0(X1)
    | v1_xboole_0(X4)
    | ~ r4_binop_1(k2_zfmisc_1(X4,X1),k6_filter_1(X4,X1,X5,X2),k6_filter_1(X4,X1,X6,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( r4_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk2_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_48])])).

cnf(c_0_66,negated_conjecture,
    ( r6_binop_1(esk2_0,esk5_0,esk6_0)
    | ~ r4_binop_1(esk2_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_10]),c_0_13]),c_0_9]),c_0_12]),c_0_11]),c_0_14])])).

cnf(c_0_67,plain,
    ( r5_binop_1(X1,X2,X3)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | ~ r5_binop_1(k2_zfmisc_1(X1,X4),k6_filter_1(X1,X4,X2,X5),k6_filter_1(X1,X4,X3,X6))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_68,negated_conjecture,
    ( r5_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_48])])).

cnf(c_0_69,plain,
    ( r4_binop_1(X1,X2,X3)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | ~ r4_binop_1(k2_zfmisc_1(X1,X4),k6_filter_1(X1,X4,X2,X5),k6_filter_1(X1,X4,X3,X6))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( r4_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | r6_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_48])])).

cnf(c_0_71,negated_conjecture,
    ( r6_binop_1(esk2_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_18]),c_0_22]),c_0_10]),c_0_13]),c_0_17]),c_0_21]),c_0_9]),c_0_12]),c_0_19]),c_0_23]),c_0_11]),c_0_14])]),c_0_54]),c_0_55]),c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( r5_binop_1(esk1_0,esk3_0,esk4_0)
    | r6_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_10]),c_0_13]),c_0_18]),c_0_22]),c_0_9]),c_0_12]),c_0_17]),c_0_21]),c_0_11]),c_0_14]),c_0_19]),c_0_23])]),c_0_55]),c_0_54])).

cnf(c_0_73,negated_conjecture,
    ( r4_binop_1(esk1_0,esk3_0,esk4_0)
    | r6_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_10]),c_0_13]),c_0_18]),c_0_22]),c_0_9]),c_0_12]),c_0_17]),c_0_21]),c_0_11]),c_0_14]),c_0_19]),c_0_23])]),c_0_55]),c_0_54])).

cnf(c_0_74,plain,
    ( r5_binop_1(k2_zfmisc_1(X1,X4),k6_filter_1(X1,X4,X2,X5),k6_filter_1(X1,X4,X3,X6))
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | ~ r5_binop_1(X1,X2,X3)
    | ~ r5_binop_1(X4,X5,X6)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_75,negated_conjecture,
    ( r5_binop_1(esk2_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_71]),c_0_10]),c_0_13]),c_0_9]),c_0_12]),c_0_11]),c_0_14])])).

cnf(c_0_76,negated_conjecture,
    ( r6_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_72]),c_0_18]),c_0_22]),c_0_17]),c_0_21]),c_0_19]),c_0_23])]),c_0_73])).

cnf(c_0_77,plain,
    ( r4_binop_1(k2_zfmisc_1(X1,X4),k6_filter_1(X1,X4,X2,X5),k6_filter_1(X1,X4,X3,X6))
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | ~ r4_binop_1(X1,X2,X3)
    | ~ r4_binop_1(X4,X5,X6)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_78,negated_conjecture,
    ( r4_binop_1(esk2_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_71]),c_0_10]),c_0_13]),c_0_9]),c_0_12]),c_0_11]),c_0_14])])).

cnf(c_0_79,negated_conjecture,
    ( r5_binop_1(k2_zfmisc_1(X1,esk2_0),k6_filter_1(X1,esk2_0,X2,esk5_0),k6_filter_1(X1,esk2_0,X3,esk6_0))
    | v1_xboole_0(X1)
    | ~ r5_binop_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_10]),c_0_13]),c_0_9]),c_0_12]),c_0_11]),c_0_14])]),c_0_55])).

cnf(c_0_80,negated_conjecture,
    ( r5_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_76]),c_0_18]),c_0_22]),c_0_17]),c_0_21]),c_0_19]),c_0_23])])).

cnf(c_0_81,negated_conjecture,
    ( r4_binop_1(k2_zfmisc_1(X1,esk2_0),k6_filter_1(X1,esk2_0,X2,esk5_0),k6_filter_1(X1,esk2_0,X3,esk6_0))
    | v1_xboole_0(X1)
    | ~ r4_binop_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_10]),c_0_13]),c_0_9]),c_0_12]),c_0_11]),c_0_14])]),c_0_55])).

cnf(c_0_82,negated_conjecture,
    ( r4_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_76]),c_0_18]),c_0_22]),c_0_17]),c_0_21]),c_0_19]),c_0_23])])).

cnf(c_0_83,negated_conjecture,
    ( ~ r6_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r6_binop_1(esk2_0,esk5_0,esk6_0)
    | ~ r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_84,negated_conjecture,
    ( r5_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_18]),c_0_22]),c_0_17]),c_0_21]),c_0_19]),c_0_23])]),c_0_54])).

cnf(c_0_85,negated_conjecture,
    ( r4_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_18]),c_0_22]),c_0_17]),c_0_21]),c_0_19]),c_0_23])]),c_0_54])).

cnf(c_0_86,negated_conjecture,
    ( ~ r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_76])]),c_0_71])])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_84]),c_0_85]),c_0_41]),c_0_48]),c_0_31]),c_0_36]),c_0_27]),c_0_28])]),c_0_86]),
    [proof]).
%------------------------------------------------------------------------------
