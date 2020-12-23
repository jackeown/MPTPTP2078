%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : filter_1__t27_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:07 EDT 2019

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   84 (2376 expanded)
%              Number of clauses        :   71 ( 761 expanded)
%              Number of leaves         :    6 ( 568 expanded)
%              Depth                    :   16
%              Number of atoms          :  478 (24882 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   37 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_filter_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ! [X4] :
                  ( m1_subset_1(X4,X2)
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) )
                         => ( ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(X2,X4,X6) )
                          <=> r3_binop_1(k2_zfmisc_1(X1,X2),k1_domain_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t27_filter_1.p',t27_filter_1)).

fof(dt_k1_domain_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X3,X1)
        & m1_subset_1(X4,X2) )
     => m1_subset_1(k1_domain_1(X1,X2,X3,X4),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t27_filter_1.p',dt_k1_domain_1)).

fof(d7_binop_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
         => ( r3_binop_1(X1,X2,X3)
          <=> ( r1_binop_1(X1,X2,X3)
              & r2_binop_1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t27_filter_1.p',d7_binop_1)).

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
    file('/export/starexec/sandbox2/benchmark/filter_1__t27_filter_1.p',dt_k6_filter_1)).

fof(t26_filter_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ! [X4] :
                  ( m1_subset_1(X4,X2)
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) )
                         => ( ( r2_binop_1(X1,X3,X5)
                              & r2_binop_1(X2,X4,X6) )
                          <=> r2_binop_1(k2_zfmisc_1(X1,X2),k1_domain_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t27_filter_1.p',t26_filter_1)).

fof(t25_filter_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ! [X4] :
                  ( m1_subset_1(X4,X2)
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) )
                         => ( ( r1_binop_1(X1,X3,X5)
                              & r1_binop_1(X2,X4,X6) )
                          <=> r1_binop_1(k2_zfmisc_1(X1,X2),k1_domain_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t27_filter_1.p',t25_filter_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( m1_subset_1(X3,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,X2)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) )
                           => ( ( r3_binop_1(X1,X3,X5)
                                & r3_binop_1(X2,X4,X6) )
                            <=> r3_binop_1(k2_zfmisc_1(X1,X2),k1_domain_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6)) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t27_filter_1])).

fof(c_0_7,plain,(
    ! [X18,X19,X20,X21] :
      ( v1_xboole_0(X18)
      | v1_xboole_0(X19)
      | ~ m1_subset_1(X20,X18)
      | ~ m1_subset_1(X21,X19)
      | m1_subset_1(k1_domain_1(X18,X19,X20,X21),k2_zfmisc_1(X18,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_domain_1])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & m1_subset_1(esk3_0,esk1_0)
    & m1_subset_1(esk4_0,esk2_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))
    & ( ~ r3_binop_1(esk1_0,esk3_0,esk5_0)
      | ~ r3_binop_1(esk2_0,esk4_0,esk6_0)
      | ~ r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0)) )
    & ( r3_binop_1(esk1_0,esk3_0,esk5_0)
      | r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0)) )
    & ( r3_binop_1(esk2_0,esk4_0,esk6_0)
      | r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])).

fof(c_0_9,plain,(
    ! [X15,X16,X17] :
      ( ( r1_binop_1(X15,X16,X17)
        | ~ r3_binop_1(X15,X16,X17)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ m1_subset_1(X16,X15) )
      & ( r2_binop_1(X15,X16,X17)
        | ~ r3_binop_1(X15,X16,X17)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ m1_subset_1(X16,X15) )
      & ( ~ r1_binop_1(X15,X16,X17)
        | ~ r2_binop_1(X15,X16,X17)
        | r3_binop_1(X15,X16,X17)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ m1_subset_1(X16,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_binop_1])])])])).

cnf(c_0_10,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_subset_1(k1_domain_1(X1,X2,X3,X4),k2_zfmisc_1(X1,X2))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X24,X25,X26,X27] :
      ( ( v1_funct_1(k6_filter_1(X24,X25,X26,X27))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,k2_zfmisc_1(X24,X24),X24)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X24,X24),X24)))
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,k2_zfmisc_1(X25,X25),X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X25,X25),X25))) )
      & ( v1_funct_2(k6_filter_1(X24,X25,X26,X27),k2_zfmisc_1(k2_zfmisc_1(X24,X25),k2_zfmisc_1(X24,X25)),k2_zfmisc_1(X24,X25))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,k2_zfmisc_1(X24,X24),X24)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X24,X24),X24)))
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,k2_zfmisc_1(X25,X25),X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X25,X25),X25))) )
      & ( m1_subset_1(k6_filter_1(X24,X25,X26,X27),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X24,X25),k2_zfmisc_1(X24,X25)),k2_zfmisc_1(X24,X25))))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,k2_zfmisc_1(X24,X24),X24)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X24,X24),X24)))
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,k2_zfmisc_1(X25,X25),X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X25,X25),X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_filter_1])])])).

cnf(c_0_14,plain,
    ( r2_binop_1(X1,X2,X3)
    | ~ r3_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r3_binop_1(esk2_0,esk4_0,esk6_0)
    | r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(k1_domain_1(X1,esk2_0,X2,esk4_0),k2_zfmisc_1(X1,esk2_0))
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( v1_funct_1(k6_filter_1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_2(esk6_0,k2_zfmisc_1(esk2_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( r2_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk2_0,esk4_0,esk6_0)
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ v1_funct_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(k6_filter_1(X1,esk2_0,X2,esk6_0))
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk5_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,plain,
    ( v1_funct_2(k6_filter_1(X1,X2,X3,X4),k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( r3_binop_1(esk1_0,esk3_0,esk5_0)
    | r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,plain,
    ( r1_binop_1(X1,X2,X3)
    | ~ r3_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( r2_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk2_0,esk4_0,esk6_0)
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ v1_funct_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(k6_filter_1(X1,esk2_0,X2,esk6_0),k2_zfmisc_1(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(X1,esk2_0)),k2_zfmisc_1(X1,esk2_0))
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_35,plain,
    ( m1_subset_1(k6_filter_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( r2_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk1_0,esk3_0,esk5_0)
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ v1_funct_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk2_0,esk4_0,esk6_0)
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ v1_funct_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( r2_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk2_0,esk4_0,esk6_0)
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k6_filter_1(X1,esk2_0,X2,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(X1,esk2_0)),k2_zfmisc_1(X1,esk2_0))))
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_41,negated_conjecture,
    ( r2_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk1_0,esk3_0,esk5_0)
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ v1_funct_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_24])])).

cnf(c_0_42,negated_conjecture,
    ( r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk2_0,esk4_0,esk6_0)
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ v1_funct_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_24])])).

fof(c_0_43,plain,(
    ! [X49,X50,X51,X52,X53,X54] :
      ( ( ~ r2_binop_1(X49,X51,X53)
        | ~ r2_binop_1(X50,X52,X54)
        | r2_binop_1(k2_zfmisc_1(X49,X50),k1_domain_1(X49,X50,X51,X52),k6_filter_1(X49,X50,X53,X54))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,k2_zfmisc_1(X50,X50),X50)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X50,X50),X50)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,k2_zfmisc_1(X49,X49),X49)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X49,X49),X49)))
        | ~ m1_subset_1(X52,X50)
        | ~ m1_subset_1(X51,X49)
        | v1_xboole_0(X50)
        | v1_xboole_0(X49) )
      & ( r2_binop_1(X49,X51,X53)
        | ~ r2_binop_1(k2_zfmisc_1(X49,X50),k1_domain_1(X49,X50,X51,X52),k6_filter_1(X49,X50,X53,X54))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,k2_zfmisc_1(X50,X50),X50)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X50,X50),X50)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,k2_zfmisc_1(X49,X49),X49)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X49,X49),X49)))
        | ~ m1_subset_1(X52,X50)
        | ~ m1_subset_1(X51,X49)
        | v1_xboole_0(X50)
        | v1_xboole_0(X49) )
      & ( r2_binop_1(X50,X52,X54)
        | ~ r2_binop_1(k2_zfmisc_1(X49,X50),k1_domain_1(X49,X50,X51,X52),k6_filter_1(X49,X50,X53,X54))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,k2_zfmisc_1(X50,X50),X50)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X50,X50),X50)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,k2_zfmisc_1(X49,X49),X49)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X49,X49),X49)))
        | ~ m1_subset_1(X52,X50)
        | ~ m1_subset_1(X51,X49)
        | v1_xboole_0(X50)
        | v1_xboole_0(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_filter_1])])])])])).

cnf(c_0_44,negated_conjecture,
    ( r2_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk2_0,esk4_0,esk6_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_46,negated_conjecture,
    ( r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk1_0,esk3_0,esk5_0)
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ v1_funct_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_47,negated_conjecture,
    ( r2_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk1_0,esk3_0,esk5_0)
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_33])])).

cnf(c_0_48,negated_conjecture,
    ( r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk2_0,esk4_0,esk6_0)
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_33])])).

cnf(c_0_49,plain,
    ( r2_binop_1(X1,X2,X3)
    | v1_xboole_0(X1)
    | v1_xboole_0(X4)
    | ~ r2_binop_1(k2_zfmisc_1(X4,X1),k1_domain_1(X4,X1,X5,X2),k6_filter_1(X4,X1,X6,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X5,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r2_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk2_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_51,negated_conjecture,
    ( r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk1_0,esk3_0,esk5_0)
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ v1_funct_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_24])])).

cnf(c_0_52,negated_conjecture,
    ( r2_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk1_0,esk3_0,esk5_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_39])])).

fof(c_0_53,plain,(
    ! [X43,X44,X45,X46,X47,X48] :
      ( ( ~ r1_binop_1(X43,X45,X47)
        | ~ r1_binop_1(X44,X46,X48)
        | r1_binop_1(k2_zfmisc_1(X43,X44),k1_domain_1(X43,X44,X45,X46),k6_filter_1(X43,X44,X47,X48))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,k2_zfmisc_1(X44,X44),X44)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X44,X44),X44)))
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,k2_zfmisc_1(X43,X43),X43)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X43,X43),X43)))
        | ~ m1_subset_1(X46,X44)
        | ~ m1_subset_1(X45,X43)
        | v1_xboole_0(X44)
        | v1_xboole_0(X43) )
      & ( r1_binop_1(X43,X45,X47)
        | ~ r1_binop_1(k2_zfmisc_1(X43,X44),k1_domain_1(X43,X44,X45,X46),k6_filter_1(X43,X44,X47,X48))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,k2_zfmisc_1(X44,X44),X44)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X44,X44),X44)))
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,k2_zfmisc_1(X43,X43),X43)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X43,X43),X43)))
        | ~ m1_subset_1(X46,X44)
        | ~ m1_subset_1(X45,X43)
        | v1_xboole_0(X44)
        | v1_xboole_0(X43) )
      & ( r1_binop_1(X44,X46,X48)
        | ~ r1_binop_1(k2_zfmisc_1(X43,X44),k1_domain_1(X43,X44,X45,X46),k6_filter_1(X43,X44,X47,X48))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,k2_zfmisc_1(X44,X44),X44)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X44,X44),X44)))
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,k2_zfmisc_1(X43,X43),X43)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X43,X43),X43)))
        | ~ m1_subset_1(X46,X44)
        | ~ m1_subset_1(X45,X43)
        | v1_xboole_0(X44)
        | v1_xboole_0(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_filter_1])])])])])).

cnf(c_0_54,negated_conjecture,
    ( r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk2_0,esk4_0,esk6_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_39])])).

cnf(c_0_55,plain,
    ( r3_binop_1(X1,X2,X3)
    | ~ r1_binop_1(X1,X2,X3)
    | ~ r2_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_56,negated_conjecture,
    ( r2_binop_1(esk2_0,esk4_0,esk6_0)
    | r3_binop_1(esk2_0,esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_26]),c_0_20]),c_0_27]),c_0_21]),c_0_28]),c_0_22]),c_0_17]),c_0_11])]),c_0_18]),c_0_12])).

cnf(c_0_57,negated_conjecture,
    ( r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk1_0,esk3_0,esk5_0)
    | ~ v1_funct_2(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_33])])).

cnf(c_0_58,plain,
    ( r2_binop_1(X1,X2,X3)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | ~ r2_binop_1(k2_zfmisc_1(X1,X4),k1_domain_1(X1,X4,X2,X5),k6_filter_1(X1,X4,X3,X6))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X5,X4)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_59,negated_conjecture,
    ( r2_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk1_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_45])])).

cnf(c_0_60,plain,
    ( r1_binop_1(X1,X2,X3)
    | v1_xboole_0(X1)
    | v1_xboole_0(X4)
    | ~ r1_binop_1(k2_zfmisc_1(X4,X1),k1_domain_1(X4,X1,X5,X2),k6_filter_1(X4,X1,X6,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X5,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk2_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_45])])).

cnf(c_0_62,negated_conjecture,
    ( r3_binop_1(esk2_0,esk4_0,esk6_0)
    | ~ r1_binop_1(esk2_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_20]),c_0_21]),c_0_22]),c_0_11])])).

cnf(c_0_63,negated_conjecture,
    ( r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk1_0,esk3_0,esk5_0)
    | ~ m1_subset_1(k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)),k2_zfmisc_1(esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_39])])).

cnf(c_0_64,negated_conjecture,
    ( r2_binop_1(esk1_0,esk3_0,esk5_0)
    | r3_binop_1(esk1_0,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_20]),c_0_26]),c_0_21]),c_0_27]),c_0_22]),c_0_28]),c_0_11]),c_0_17])]),c_0_12]),c_0_18])).

cnf(c_0_65,negated_conjecture,
    ( r3_binop_1(esk2_0,esk4_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_26]),c_0_20]),c_0_27]),c_0_21]),c_0_28]),c_0_22]),c_0_17]),c_0_11])]),c_0_18]),c_0_12]),c_0_62])).

cnf(c_0_66,plain,
    ( r1_binop_1(X1,X2,X3)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | ~ r1_binop_1(k2_zfmisc_1(X1,X4),k1_domain_1(X1,X4,X2,X5),k6_filter_1(X1,X4,X3,X6))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X5,X4)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_67,negated_conjecture,
    ( r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk1_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_45])])).

cnf(c_0_68,negated_conjecture,
    ( r3_binop_1(esk1_0,esk3_0,esk5_0)
    | ~ r1_binop_1(esk1_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_64]),c_0_26]),c_0_27]),c_0_28]),c_0_17])])).

cnf(c_0_69,plain,
    ( r2_binop_1(k2_zfmisc_1(X1,X4),k1_domain_1(X1,X4,X2,X5),k6_filter_1(X1,X4,X3,X6))
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | ~ r2_binop_1(X1,X2,X3)
    | ~ r2_binop_1(X4,X5,X6)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X5,X4)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_70,negated_conjecture,
    ( r2_binop_1(esk2_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_65]),c_0_20]),c_0_21]),c_0_22]),c_0_11])])).

cnf(c_0_71,negated_conjecture,
    ( r3_binop_1(esk1_0,esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_20]),c_0_26]),c_0_21]),c_0_27]),c_0_22]),c_0_28]),c_0_11]),c_0_17])]),c_0_12]),c_0_18]),c_0_68])).

cnf(c_0_72,plain,
    ( r1_binop_1(k2_zfmisc_1(X1,X4),k1_domain_1(X1,X4,X2,X5),k6_filter_1(X1,X4,X3,X6))
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | ~ r1_binop_1(X1,X2,X3)
    | ~ r1_binop_1(X4,X5,X6)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X5,X4)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_73,negated_conjecture,
    ( r1_binop_1(esk2_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_65]),c_0_20]),c_0_21]),c_0_22]),c_0_11])])).

cnf(c_0_74,negated_conjecture,
    ( ~ r3_binop_1(esk1_0,esk3_0,esk5_0)
    | ~ r3_binop_1(esk2_0,esk4_0,esk6_0)
    | ~ r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_75,negated_conjecture,
    ( r2_binop_1(k2_zfmisc_1(X1,esk2_0),k1_domain_1(X1,esk2_0,X2,esk4_0),k6_filter_1(X1,esk2_0,X3,esk6_0))
    | v1_xboole_0(X1)
    | ~ r2_binop_1(X1,X2,X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_20]),c_0_21]),c_0_22]),c_0_11])]),c_0_12])).

cnf(c_0_76,negated_conjecture,
    ( r2_binop_1(esk1_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_71]),c_0_26]),c_0_27]),c_0_28]),c_0_17])])).

cnf(c_0_77,negated_conjecture,
    ( r1_binop_1(k2_zfmisc_1(X1,esk2_0),k1_domain_1(X1,esk2_0,X2,esk4_0),k6_filter_1(X1,esk2_0,X3,esk6_0))
    | v1_xboole_0(X1)
    | ~ r1_binop_1(X1,X2,X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_20]),c_0_21]),c_0_22]),c_0_11])]),c_0_12])).

cnf(c_0_78,negated_conjecture,
    ( r1_binop_1(esk1_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_71]),c_0_26]),c_0_27]),c_0_28]),c_0_17])])).

cnf(c_0_79,negated_conjecture,
    ( ~ r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | ~ r3_binop_1(esk2_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_71])])).

cnf(c_0_80,negated_conjecture,
    ( r2_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_26]),c_0_27]),c_0_28]),c_0_17])]),c_0_18])).

cnf(c_0_81,negated_conjecture,
    ( r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_26]),c_0_27]),c_0_28]),c_0_17])]),c_0_18])).

cnf(c_0_82,negated_conjecture,
    ( ~ r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_65])])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_80]),c_0_81]),c_0_39]),c_0_33]),c_0_45]),c_0_24])]),c_0_82]),
    [proof]).
%------------------------------------------------------------------------------
