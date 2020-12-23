%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:52 EST 2020

% Result     : Theorem 1.19s
% Output     : CNFRefutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   73 (1643 expanded)
%              Number of clauses        :   60 ( 502 expanded)
%              Number of leaves         :    6 ( 410 expanded)
%              Depth                    :   15
%              Number of atoms          :  472 (17706 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal clause size      :   37 (   4 average)
%              Maximal term depth       :    5 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_filter_1)).

fof(dt_k1_domain_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X3,X1)
        & m1_subset_1(X4,X2) )
     => m1_subset_1(k1_domain_1(X1,X2,X3,X4),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_domain_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_binop_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_filter_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_filter_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_filter_1)).

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
    ! [X7,X8,X9,X10] :
      ( v1_xboole_0(X7)
      | v1_xboole_0(X8)
      | ~ m1_subset_1(X9,X7)
      | ~ m1_subset_1(X10,X8)
      | m1_subset_1(k1_domain_1(X7,X8,X9,X10),k2_zfmisc_1(X7,X8)) ) ),
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
    ! [X11,X12,X13] :
      ( ( r1_binop_1(X11,X12,X13)
        | ~ r3_binop_1(X11,X12,X13)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,k2_zfmisc_1(X11,X11),X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11)))
        | ~ m1_subset_1(X12,X11) )
      & ( r2_binop_1(X11,X12,X13)
        | ~ r3_binop_1(X11,X12,X13)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,k2_zfmisc_1(X11,X11),X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11)))
        | ~ m1_subset_1(X12,X11) )
      & ( ~ r1_binop_1(X11,X12,X13)
        | ~ r2_binop_1(X11,X12,X13)
        | r3_binop_1(X11,X12,X13)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,k2_zfmisc_1(X11,X11),X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11)))
        | ~ m1_subset_1(X12,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_binop_1])])])])).

fof(c_0_10,plain,(
    ! [X14,X15,X16,X17] :
      ( ( v1_funct_1(k6_filter_1(X14,X15,X16,X17))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,k2_zfmisc_1(X14,X14),X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15))) )
      & ( v1_funct_2(k6_filter_1(X14,X15,X16,X17),k2_zfmisc_1(k2_zfmisc_1(X14,X15),k2_zfmisc_1(X14,X15)),k2_zfmisc_1(X14,X15))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,k2_zfmisc_1(X14,X14),X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15))) )
      & ( m1_subset_1(k6_filter_1(X14,X15,X16,X17),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X15),k2_zfmisc_1(X14,X15)),k2_zfmisc_1(X14,X15))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,k2_zfmisc_1(X14,X14),X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_filter_1])])])).

cnf(c_0_11,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | m1_subset_1(k1_domain_1(X1,X2,X3,X4),k2_zfmisc_1(X1,X2))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_binop_1(X1,X2,X3)
    | ~ r3_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( m1_subset_1(k6_filter_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v1_funct_1(k6_filter_1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v1_funct_2(k6_filter_1(X1,X2,X3,X4),k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(k1_domain_1(X1,esk2_0,X2,esk4_0),k2_zfmisc_1(X1,esk2_0))
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( r1_binop_1(X1,X2,X3)
    | ~ r3_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_22,plain,(
    ! [X24,X25,X26,X27,X28,X29] :
      ( ( ~ r2_binop_1(X24,X26,X28)
        | ~ r2_binop_1(X25,X27,X29)
        | r2_binop_1(k2_zfmisc_1(X24,X25),k1_domain_1(X24,X25,X26,X27),k6_filter_1(X24,X25,X28,X29))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,k2_zfmisc_1(X25,X25),X25)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X25,X25),X25)))
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,k2_zfmisc_1(X24,X24),X24)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X24,X24),X24)))
        | ~ m1_subset_1(X27,X25)
        | ~ m1_subset_1(X26,X24)
        | v1_xboole_0(X25)
        | v1_xboole_0(X24) )
      & ( r2_binop_1(X24,X26,X28)
        | ~ r2_binop_1(k2_zfmisc_1(X24,X25),k1_domain_1(X24,X25,X26,X27),k6_filter_1(X24,X25,X28,X29))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,k2_zfmisc_1(X25,X25),X25)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X25,X25),X25)))
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,k2_zfmisc_1(X24,X24),X24)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X24,X24),X24)))
        | ~ m1_subset_1(X27,X25)
        | ~ m1_subset_1(X26,X24)
        | v1_xboole_0(X25)
        | v1_xboole_0(X24) )
      & ( r2_binop_1(X25,X27,X29)
        | ~ r2_binop_1(k2_zfmisc_1(X24,X25),k1_domain_1(X24,X25,X26,X27),k6_filter_1(X24,X25,X28,X29))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,k2_zfmisc_1(X25,X25),X25)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X25,X25),X25)))
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,k2_zfmisc_1(X24,X24),X24)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X24,X24),X24)))
        | ~ m1_subset_1(X27,X25)
        | ~ m1_subset_1(X26,X24)
        | v1_xboole_0(X25)
        | v1_xboole_0(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_filter_1])])])])])).

cnf(c_0_23,plain,
    ( r2_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))
    | ~ r3_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))
    | ~ v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X3,k2_zfmisc_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r3_binop_1(esk1_0,esk3_0,esk5_0)
    | r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk6_0,k2_zfmisc_1(esk2_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk5_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

fof(c_0_32,plain,(
    ! [X18,X19,X20,X21,X22,X23] :
      ( ( ~ r1_binop_1(X18,X20,X22)
        | ~ r1_binop_1(X19,X21,X23)
        | r1_binop_1(k2_zfmisc_1(X18,X19),k1_domain_1(X18,X19,X20,X21),k6_filter_1(X18,X19,X22,X23))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,k2_zfmisc_1(X19,X19),X19)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X19,X19),X19)))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,k2_zfmisc_1(X18,X18),X18)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X18,X18),X18)))
        | ~ m1_subset_1(X21,X19)
        | ~ m1_subset_1(X20,X18)
        | v1_xboole_0(X19)
        | v1_xboole_0(X18) )
      & ( r1_binop_1(X18,X20,X22)
        | ~ r1_binop_1(k2_zfmisc_1(X18,X19),k1_domain_1(X18,X19,X20,X21),k6_filter_1(X18,X19,X22,X23))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,k2_zfmisc_1(X19,X19),X19)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X19,X19),X19)))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,k2_zfmisc_1(X18,X18),X18)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X18,X18),X18)))
        | ~ m1_subset_1(X21,X19)
        | ~ m1_subset_1(X20,X18)
        | v1_xboole_0(X19)
        | v1_xboole_0(X18) )
      & ( r1_binop_1(X19,X21,X23)
        | ~ r1_binop_1(k2_zfmisc_1(X18,X19),k1_domain_1(X18,X19,X20,X21),k6_filter_1(X18,X19,X22,X23))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,k2_zfmisc_1(X19,X19),X19)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X19,X19),X19)))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,k2_zfmisc_1(X18,X18),X18)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X18,X18),X18)))
        | ~ m1_subset_1(X21,X19)
        | ~ m1_subset_1(X20,X18)
        | v1_xboole_0(X19)
        | v1_xboole_0(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_filter_1])])])])])).

cnf(c_0_33,plain,
    ( r1_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))
    | ~ r3_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))
    | ~ v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X3,k2_zfmisc_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_34,plain,
    ( r3_binop_1(X1,X2,X3)
    | ~ r1_binop_1(X1,X2,X3)
    | ~ r2_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( r2_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk1_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_37,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk1_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_39,negated_conjecture,
    ( r3_binop_1(esk2_0,esk4_0,esk6_0)
    | r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_40,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,negated_conjecture,
    ( r3_binop_1(esk1_0,X1,esk5_0)
    | ~ r2_binop_1(esk1_0,X1,esk5_0)
    | ~ r1_binop_1(esk1_0,X1,esk5_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_30]),c_0_26]),c_0_28])])).

cnf(c_0_42,negated_conjecture,
    ( r2_binop_1(esk1_0,esk3_0,esk5_0)
    | r3_binop_1(esk1_0,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_12]),c_0_19])]),c_0_13]),c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( r1_binop_1(esk1_0,esk3_0,esk5_0)
    | r3_binop_1(esk1_0,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_12]),c_0_19])]),c_0_13]),c_0_20])).

cnf(c_0_44,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_45,negated_conjecture,
    ( r2_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk2_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_39]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_46,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | r3_binop_1(esk2_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_39]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_48,negated_conjecture,
    ( r2_binop_1(k2_zfmisc_1(X1,esk2_0),k1_domain_1(X1,esk2_0,X2,X3),k6_filter_1(X1,esk2_0,X4,esk6_0))
    | v1_xboole_0(X1)
    | ~ r2_binop_1(esk2_0,X3,esk6_0)
    | ~ r2_binop_1(X1,X2,X4)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X3,esk2_0)
    | ~ m1_subset_1(X2,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_29]),c_0_25]),c_0_27])]),c_0_13])).

cnf(c_0_49,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_50,negated_conjecture,
    ( ~ r3_binop_1(esk1_0,esk3_0,esk5_0)
    | ~ r3_binop_1(esk2_0,esk4_0,esk6_0)
    | ~ r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_51,negated_conjecture,
    ( r3_binop_1(esk1_0,esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_19])]),c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( r3_binop_1(esk2_0,X1,esk6_0)
    | ~ r2_binop_1(esk2_0,X1,esk6_0)
    | ~ r1_binop_1(esk2_0,X1,esk6_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_29]),c_0_25]),c_0_27])])).

cnf(c_0_53,negated_conjecture,
    ( r2_binop_1(esk2_0,esk4_0,esk6_0)
    | r3_binop_1(esk2_0,esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_26]),c_0_25]),c_0_28]),c_0_27]),c_0_30]),c_0_29]),c_0_19]),c_0_12])]),c_0_20]),c_0_13])).

cnf(c_0_54,negated_conjecture,
    ( r1_binop_1(esk2_0,esk4_0,esk6_0)
    | r3_binop_1(esk2_0,esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_26]),c_0_25]),c_0_28]),c_0_27]),c_0_30]),c_0_29]),c_0_19]),c_0_12])]),c_0_20]),c_0_13])).

cnf(c_0_55,plain,
    ( r3_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))
    | ~ r2_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))
    | ~ r1_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))
    | ~ v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X3,k2_zfmisc_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_56,negated_conjecture,
    ( r2_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,X1,X2),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | ~ r2_binop_1(esk2_0,X2,esk6_0)
    | ~ r2_binop_1(esk1_0,X1,esk5_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_30]),c_0_26]),c_0_28])]),c_0_20])).

cnf(c_0_57,negated_conjecture,
    ( r1_binop_1(k2_zfmisc_1(X1,esk2_0),k1_domain_1(X1,esk2_0,X2,X3),k6_filter_1(X1,esk2_0,X4,esk6_0))
    | v1_xboole_0(X1)
    | ~ r1_binop_1(esk2_0,X3,esk6_0)
    | ~ r1_binop_1(X1,X2,X4)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X3,esk2_0)
    | ~ m1_subset_1(X2,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_29]),c_0_25]),c_0_27])]),c_0_13])).

cnf(c_0_58,negated_conjecture,
    ( ~ r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | ~ r3_binop_1(esk2_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])])).

cnf(c_0_59,negated_conjecture,
    ( r3_binop_1(esk2_0,esk4_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_12])]),c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,X1,X2),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | ~ r2_binop_1(esk2_0,X2,esk6_0)
    | ~ r2_binop_1(esk1_0,X1,esk5_0)
    | ~ r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,X1,X2),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | ~ m1_subset_1(k1_domain_1(esk1_0,esk2_0,X1,X2),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_61,negated_conjecture,
    ( r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,X1,X2),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | ~ r1_binop_1(esk2_0,X2,esk6_0)
    | ~ r1_binop_1(esk1_0,X1,esk5_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_30]),c_0_26]),c_0_28])]),c_0_20])).

cnf(c_0_62,negated_conjecture,
    ( ~ r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_63,negated_conjecture,
    ( r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,X1,X2),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))
    | ~ r2_binop_1(esk2_0,X2,esk6_0)
    | ~ r2_binop_1(esk1_0,X1,esk5_0)
    | ~ r1_binop_1(esk2_0,X2,esk6_0)
    | ~ r1_binop_1(esk1_0,X1,esk5_0)
    | ~ m1_subset_1(k1_domain_1(esk1_0,esk2_0,X1,X2),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_binop_1(esk2_0,esk4_0,esk6_0)
    | ~ r2_binop_1(esk1_0,esk3_0,esk5_0)
    | ~ r1_binop_1(esk2_0,esk4_0,esk6_0)
    | ~ r1_binop_1(esk1_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_31]),c_0_12]),c_0_19])])).

cnf(c_0_65,negated_conjecture,
    ( r2_binop_1(esk2_0,X1,esk6_0)
    | ~ r3_binop_1(esk2_0,X1,esk6_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_29]),c_0_25]),c_0_27])])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_binop_1(esk1_0,esk3_0,esk5_0)
    | ~ r1_binop_1(esk2_0,esk4_0,esk6_0)
    | ~ r1_binop_1(esk1_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_59]),c_0_12])])).

cnf(c_0_67,negated_conjecture,
    ( r2_binop_1(esk1_0,X1,esk5_0)
    | ~ r3_binop_1(esk1_0,X1,esk5_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_30]),c_0_26]),c_0_28])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_binop_1(esk2_0,esk4_0,esk6_0)
    | ~ r1_binop_1(esk1_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_51]),c_0_19])])).

cnf(c_0_69,negated_conjecture,
    ( r1_binop_1(esk2_0,X1,esk6_0)
    | ~ r3_binop_1(esk2_0,X1,esk6_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_29]),c_0_25]),c_0_27])])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_binop_1(esk1_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_59]),c_0_12])])).

cnf(c_0_71,negated_conjecture,
    ( r1_binop_1(esk1_0,X1,esk5_0)
    | ~ r3_binop_1(esk1_0,X1,esk5_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_30]),c_0_26]),c_0_28])])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_51]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:32:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.19/1.34  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.19/1.34  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.19/1.34  #
% 1.19/1.34  # Preprocessing time       : 0.029 s
% 1.19/1.34  # Presaturation interreduction done
% 1.19/1.34  
% 1.19/1.34  # Proof found!
% 1.19/1.34  # SZS status Theorem
% 1.19/1.34  # SZS output start CNFRefutation
% 1.19/1.34  fof(t27_filter_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m1_subset_1(X4,X2)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))))=>((r3_binop_1(X1,X3,X5)&r3_binop_1(X2,X4,X6))<=>r3_binop_1(k2_zfmisc_1(X1,X2),k1_domain_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_filter_1)).
% 1.19/1.34  fof(dt_k1_domain_1, axiom, ![X1, X2, X3, X4]:((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X3,X1))&m1_subset_1(X4,X2))=>m1_subset_1(k1_domain_1(X1,X2,X3,X4),k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_domain_1)).
% 1.19/1.34  fof(d7_binop_1, axiom, ![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>(r3_binop_1(X1,X2,X3)<=>(r1_binop_1(X1,X2,X3)&r2_binop_1(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_binop_1)).
% 1.19/1.34  fof(dt_k6_filter_1, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))&v1_funct_1(X4))&v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))))=>((v1_funct_1(k6_filter_1(X1,X2,X3,X4))&v1_funct_2(k6_filter_1(X1,X2,X3,X4),k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2)))&m1_subset_1(k6_filter_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_filter_1)).
% 1.19/1.34  fof(t26_filter_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m1_subset_1(X4,X2)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))))=>((r2_binop_1(X1,X3,X5)&r2_binop_1(X2,X4,X6))<=>r2_binop_1(k2_zfmisc_1(X1,X2),k1_domain_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_filter_1)).
% 1.19/1.34  fof(t25_filter_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m1_subset_1(X4,X2)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))))=>((r1_binop_1(X1,X3,X5)&r1_binop_1(X2,X4,X6))<=>r1_binop_1(k2_zfmisc_1(X1,X2),k1_domain_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_filter_1)).
% 1.19/1.34  fof(c_0_6, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m1_subset_1(X4,X2)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))))=>((r3_binop_1(X1,X3,X5)&r3_binop_1(X2,X4,X6))<=>r3_binop_1(k2_zfmisc_1(X1,X2),k1_domain_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6)))))))))), inference(assume_negation,[status(cth)],[t27_filter_1])).
% 1.19/1.34  fof(c_0_7, plain, ![X7, X8, X9, X10]:(v1_xboole_0(X7)|v1_xboole_0(X8)|~m1_subset_1(X9,X7)|~m1_subset_1(X10,X8)|m1_subset_1(k1_domain_1(X7,X8,X9,X10),k2_zfmisc_1(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_domain_1])])])).
% 1.19/1.34  fof(c_0_8, negated_conjecture, (~v1_xboole_0(esk1_0)&(~v1_xboole_0(esk2_0)&(m1_subset_1(esk3_0,esk1_0)&(m1_subset_1(esk4_0,esk2_0)&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,k2_zfmisc_1(esk2_0,esk2_0),esk2_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0))))&((~r3_binop_1(esk1_0,esk3_0,esk5_0)|~r3_binop_1(esk2_0,esk4_0,esk6_0)|~r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0)))&((r3_binop_1(esk1_0,esk3_0,esk5_0)|r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0)))&(r3_binop_1(esk2_0,esk4_0,esk6_0)|r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])).
% 1.19/1.34  fof(c_0_9, plain, ![X11, X12, X13]:(((r1_binop_1(X11,X12,X13)|~r3_binop_1(X11,X12,X13)|(~v1_funct_1(X13)|~v1_funct_2(X13,k2_zfmisc_1(X11,X11),X11)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11))))|~m1_subset_1(X12,X11))&(r2_binop_1(X11,X12,X13)|~r3_binop_1(X11,X12,X13)|(~v1_funct_1(X13)|~v1_funct_2(X13,k2_zfmisc_1(X11,X11),X11)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11))))|~m1_subset_1(X12,X11)))&(~r1_binop_1(X11,X12,X13)|~r2_binop_1(X11,X12,X13)|r3_binop_1(X11,X12,X13)|(~v1_funct_1(X13)|~v1_funct_2(X13,k2_zfmisc_1(X11,X11),X11)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11))))|~m1_subset_1(X12,X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_binop_1])])])])).
% 1.19/1.34  fof(c_0_10, plain, ![X14, X15, X16, X17]:(((v1_funct_1(k6_filter_1(X14,X15,X16,X17))|(~v1_funct_1(X16)|~v1_funct_2(X16,k2_zfmisc_1(X14,X14),X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14)))|~v1_funct_1(X17)|~v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))))&(v1_funct_2(k6_filter_1(X14,X15,X16,X17),k2_zfmisc_1(k2_zfmisc_1(X14,X15),k2_zfmisc_1(X14,X15)),k2_zfmisc_1(X14,X15))|(~v1_funct_1(X16)|~v1_funct_2(X16,k2_zfmisc_1(X14,X14),X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14)))|~v1_funct_1(X17)|~v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15))))))&(m1_subset_1(k6_filter_1(X14,X15,X16,X17),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X15),k2_zfmisc_1(X14,X15)),k2_zfmisc_1(X14,X15))))|(~v1_funct_1(X16)|~v1_funct_2(X16,k2_zfmisc_1(X14,X14),X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14)))|~v1_funct_1(X17)|~v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_filter_1])])])).
% 1.19/1.34  cnf(c_0_11, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|m1_subset_1(k1_domain_1(X1,X2,X3,X4),k2_zfmisc_1(X1,X2))|~m1_subset_1(X3,X1)|~m1_subset_1(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.19/1.34  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.19/1.34  cnf(c_0_13, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.19/1.34  cnf(c_0_14, plain, (r2_binop_1(X1,X2,X3)|~r3_binop_1(X1,X2,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.19/1.34  cnf(c_0_15, plain, (m1_subset_1(k6_filter_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X4)|~v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.19/1.34  cnf(c_0_16, plain, (v1_funct_1(k6_filter_1(X1,X2,X3,X4))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X4)|~v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.19/1.34  cnf(c_0_17, plain, (v1_funct_2(k6_filter_1(X1,X2,X3,X4),k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X4)|~v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.19/1.34  cnf(c_0_18, negated_conjecture, (m1_subset_1(k1_domain_1(X1,esk2_0,X2,esk4_0),k2_zfmisc_1(X1,esk2_0))|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])).
% 1.19/1.34  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.19/1.34  cnf(c_0_20, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.19/1.34  cnf(c_0_21, plain, (r1_binop_1(X1,X2,X3)|~r3_binop_1(X1,X2,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.19/1.34  fof(c_0_22, plain, ![X24, X25, X26, X27, X28, X29]:((~r2_binop_1(X24,X26,X28)|~r2_binop_1(X25,X27,X29)|r2_binop_1(k2_zfmisc_1(X24,X25),k1_domain_1(X24,X25,X26,X27),k6_filter_1(X24,X25,X28,X29))|(~v1_funct_1(X29)|~v1_funct_2(X29,k2_zfmisc_1(X25,X25),X25)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X25,X25),X25))))|(~v1_funct_1(X28)|~v1_funct_2(X28,k2_zfmisc_1(X24,X24),X24)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X24,X24),X24))))|~m1_subset_1(X27,X25)|~m1_subset_1(X26,X24)|v1_xboole_0(X25)|v1_xboole_0(X24))&((r2_binop_1(X24,X26,X28)|~r2_binop_1(k2_zfmisc_1(X24,X25),k1_domain_1(X24,X25,X26,X27),k6_filter_1(X24,X25,X28,X29))|(~v1_funct_1(X29)|~v1_funct_2(X29,k2_zfmisc_1(X25,X25),X25)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X25,X25),X25))))|(~v1_funct_1(X28)|~v1_funct_2(X28,k2_zfmisc_1(X24,X24),X24)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X24,X24),X24))))|~m1_subset_1(X27,X25)|~m1_subset_1(X26,X24)|v1_xboole_0(X25)|v1_xboole_0(X24))&(r2_binop_1(X25,X27,X29)|~r2_binop_1(k2_zfmisc_1(X24,X25),k1_domain_1(X24,X25,X26,X27),k6_filter_1(X24,X25,X28,X29))|(~v1_funct_1(X29)|~v1_funct_2(X29,k2_zfmisc_1(X25,X25),X25)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X25,X25),X25))))|(~v1_funct_1(X28)|~v1_funct_2(X28,k2_zfmisc_1(X24,X24),X24)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X24,X24),X24))))|~m1_subset_1(X27,X25)|~m1_subset_1(X26,X24)|v1_xboole_0(X25)|v1_xboole_0(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_filter_1])])])])])).
% 1.19/1.34  cnf(c_0_23, plain, (r2_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))|~r3_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))|~v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X5)|~v1_funct_1(X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X3,k2_zfmisc_1(X1,X2))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])).
% 1.19/1.34  cnf(c_0_24, negated_conjecture, (r3_binop_1(esk1_0,esk3_0,esk5_0)|r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.19/1.34  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk6_0,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.19/1.34  cnf(c_0_26, negated_conjecture, (v1_funct_2(esk5_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.19/1.34  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.19/1.34  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.19/1.34  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.19/1.34  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.19/1.34  cnf(c_0_31, negated_conjecture, (m1_subset_1(k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k2_zfmisc_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 1.19/1.34  fof(c_0_32, plain, ![X18, X19, X20, X21, X22, X23]:((~r1_binop_1(X18,X20,X22)|~r1_binop_1(X19,X21,X23)|r1_binop_1(k2_zfmisc_1(X18,X19),k1_domain_1(X18,X19,X20,X21),k6_filter_1(X18,X19,X22,X23))|(~v1_funct_1(X23)|~v1_funct_2(X23,k2_zfmisc_1(X19,X19),X19)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X19,X19),X19))))|(~v1_funct_1(X22)|~v1_funct_2(X22,k2_zfmisc_1(X18,X18),X18)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X18,X18),X18))))|~m1_subset_1(X21,X19)|~m1_subset_1(X20,X18)|v1_xboole_0(X19)|v1_xboole_0(X18))&((r1_binop_1(X18,X20,X22)|~r1_binop_1(k2_zfmisc_1(X18,X19),k1_domain_1(X18,X19,X20,X21),k6_filter_1(X18,X19,X22,X23))|(~v1_funct_1(X23)|~v1_funct_2(X23,k2_zfmisc_1(X19,X19),X19)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X19,X19),X19))))|(~v1_funct_1(X22)|~v1_funct_2(X22,k2_zfmisc_1(X18,X18),X18)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X18,X18),X18))))|~m1_subset_1(X21,X19)|~m1_subset_1(X20,X18)|v1_xboole_0(X19)|v1_xboole_0(X18))&(r1_binop_1(X19,X21,X23)|~r1_binop_1(k2_zfmisc_1(X18,X19),k1_domain_1(X18,X19,X20,X21),k6_filter_1(X18,X19,X22,X23))|(~v1_funct_1(X23)|~v1_funct_2(X23,k2_zfmisc_1(X19,X19),X19)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X19,X19),X19))))|(~v1_funct_1(X22)|~v1_funct_2(X22,k2_zfmisc_1(X18,X18),X18)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X18,X18),X18))))|~m1_subset_1(X21,X19)|~m1_subset_1(X20,X18)|v1_xboole_0(X19)|v1_xboole_0(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_filter_1])])])])])).
% 1.19/1.34  cnf(c_0_33, plain, (r1_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))|~r3_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))|~v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X5)|~v1_funct_1(X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X3,k2_zfmisc_1(X1,X2))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_15]), c_0_16]), c_0_17])).
% 1.19/1.34  cnf(c_0_34, plain, (r3_binop_1(X1,X2,X3)|~r1_binop_1(X1,X2,X3)|~r2_binop_1(X1,X2,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.19/1.34  cnf(c_0_35, plain, (r2_binop_1(X1,X2,X3)|v1_xboole_0(X4)|v1_xboole_0(X1)|~r2_binop_1(k2_zfmisc_1(X1,X4),k1_domain_1(X1,X4,X2,X5),k6_filter_1(X1,X4,X3,X6))|~v1_funct_1(X6)|~v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X5,X4)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.19/1.34  cnf(c_0_36, negated_conjecture, (r2_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))|r3_binop_1(esk1_0,esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])])).
% 1.19/1.34  cnf(c_0_37, plain, (r1_binop_1(X1,X2,X3)|v1_xboole_0(X4)|v1_xboole_0(X1)|~r1_binop_1(k2_zfmisc_1(X1,X4),k1_domain_1(X1,X4,X2,X5),k6_filter_1(X1,X4,X3,X6))|~v1_funct_1(X6)|~v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X5,X4)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.19/1.34  cnf(c_0_38, negated_conjecture, (r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))|r3_binop_1(esk1_0,esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])])).
% 1.19/1.34  cnf(c_0_39, negated_conjecture, (r3_binop_1(esk2_0,esk4_0,esk6_0)|r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.19/1.34  cnf(c_0_40, plain, (r2_binop_1(k2_zfmisc_1(X1,X4),k1_domain_1(X1,X4,X2,X5),k6_filter_1(X1,X4,X3,X6))|v1_xboole_0(X4)|v1_xboole_0(X1)|~r2_binop_1(X1,X2,X3)|~r2_binop_1(X4,X5,X6)|~v1_funct_1(X6)|~v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X5,X4)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.19/1.34  cnf(c_0_41, negated_conjecture, (r3_binop_1(esk1_0,X1,esk5_0)|~r2_binop_1(esk1_0,X1,esk5_0)|~r1_binop_1(esk1_0,X1,esk5_0)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_30]), c_0_26]), c_0_28])])).
% 1.19/1.34  cnf(c_0_42, negated_conjecture, (r2_binop_1(esk1_0,esk3_0,esk5_0)|r3_binop_1(esk1_0,esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_12]), c_0_19])]), c_0_13]), c_0_20])).
% 1.19/1.34  cnf(c_0_43, negated_conjecture, (r1_binop_1(esk1_0,esk3_0,esk5_0)|r3_binop_1(esk1_0,esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_12]), c_0_19])]), c_0_13]), c_0_20])).
% 1.19/1.34  cnf(c_0_44, plain, (r2_binop_1(X1,X2,X3)|v1_xboole_0(X1)|v1_xboole_0(X4)|~r2_binop_1(k2_zfmisc_1(X4,X1),k1_domain_1(X4,X1,X5,X2),k6_filter_1(X4,X1,X6,X3))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X6)|~v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))|~m1_subset_1(X2,X1)|~m1_subset_1(X5,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.19/1.34  cnf(c_0_45, negated_conjecture, (r2_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))|r3_binop_1(esk2_0,esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_39]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])])).
% 1.19/1.34  cnf(c_0_46, plain, (r1_binop_1(X1,X2,X3)|v1_xboole_0(X1)|v1_xboole_0(X4)|~r1_binop_1(k2_zfmisc_1(X4,X1),k1_domain_1(X4,X1,X5,X2),k6_filter_1(X4,X1,X6,X3))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X6)|~v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))|~m1_subset_1(X2,X1)|~m1_subset_1(X5,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.19/1.34  cnf(c_0_47, negated_conjecture, (r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))|r3_binop_1(esk2_0,esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_39]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])])).
% 1.19/1.34  cnf(c_0_48, negated_conjecture, (r2_binop_1(k2_zfmisc_1(X1,esk2_0),k1_domain_1(X1,esk2_0,X2,X3),k6_filter_1(X1,esk2_0,X4,esk6_0))|v1_xboole_0(X1)|~r2_binop_1(esk2_0,X3,esk6_0)|~r2_binop_1(X1,X2,X4)|~v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X3,esk2_0)|~m1_subset_1(X2,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_29]), c_0_25]), c_0_27])]), c_0_13])).
% 1.19/1.34  cnf(c_0_49, plain, (r1_binop_1(k2_zfmisc_1(X1,X4),k1_domain_1(X1,X4,X2,X5),k6_filter_1(X1,X4,X3,X6))|v1_xboole_0(X4)|v1_xboole_0(X1)|~r1_binop_1(X1,X2,X3)|~r1_binop_1(X4,X5,X6)|~v1_funct_1(X6)|~v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X5,X4)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.19/1.34  cnf(c_0_50, negated_conjecture, (~r3_binop_1(esk1_0,esk3_0,esk5_0)|~r3_binop_1(esk2_0,esk4_0,esk6_0)|~r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.19/1.34  cnf(c_0_51, negated_conjecture, (r3_binop_1(esk1_0,esk3_0,esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_19])]), c_0_43])).
% 1.19/1.34  cnf(c_0_52, negated_conjecture, (r3_binop_1(esk2_0,X1,esk6_0)|~r2_binop_1(esk2_0,X1,esk6_0)|~r1_binop_1(esk2_0,X1,esk6_0)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_29]), c_0_25]), c_0_27])])).
% 1.19/1.34  cnf(c_0_53, negated_conjecture, (r2_binop_1(esk2_0,esk4_0,esk6_0)|r3_binop_1(esk2_0,esk4_0,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_26]), c_0_25]), c_0_28]), c_0_27]), c_0_30]), c_0_29]), c_0_19]), c_0_12])]), c_0_20]), c_0_13])).
% 1.19/1.34  cnf(c_0_54, negated_conjecture, (r1_binop_1(esk2_0,esk4_0,esk6_0)|r3_binop_1(esk2_0,esk4_0,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_26]), c_0_25]), c_0_28]), c_0_27]), c_0_30]), c_0_29]), c_0_19]), c_0_12])]), c_0_20]), c_0_13])).
% 1.19/1.34  cnf(c_0_55, plain, (r3_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))|~r2_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))|~r1_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))|~v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X5)|~v1_funct_1(X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X3,k2_zfmisc_1(X1,X2))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_15]), c_0_16]), c_0_17])).
% 1.19/1.34  cnf(c_0_56, negated_conjecture, (r2_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,X1,X2),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))|~r2_binop_1(esk2_0,X2,esk6_0)|~r2_binop_1(esk1_0,X1,esk5_0)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_30]), c_0_26]), c_0_28])]), c_0_20])).
% 1.19/1.34  cnf(c_0_57, negated_conjecture, (r1_binop_1(k2_zfmisc_1(X1,esk2_0),k1_domain_1(X1,esk2_0,X2,X3),k6_filter_1(X1,esk2_0,X4,esk6_0))|v1_xboole_0(X1)|~r1_binop_1(esk2_0,X3,esk6_0)|~r1_binop_1(X1,X2,X4)|~v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X3,esk2_0)|~m1_subset_1(X2,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_29]), c_0_25]), c_0_27])]), c_0_13])).
% 1.19/1.34  cnf(c_0_58, negated_conjecture, (~r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))|~r3_binop_1(esk2_0,esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51])])).
% 1.19/1.34  cnf(c_0_59, negated_conjecture, (r3_binop_1(esk2_0,esk4_0,esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_12])]), c_0_54])).
% 1.19/1.34  cnf(c_0_60, negated_conjecture, (r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,X1,X2),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))|~r2_binop_1(esk2_0,X2,esk6_0)|~r2_binop_1(esk1_0,X1,esk5_0)|~r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,X1,X2),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))|~m1_subset_1(k1_domain_1(esk1_0,esk2_0,X1,X2),k2_zfmisc_1(esk1_0,esk2_0))|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])])).
% 1.19/1.34  cnf(c_0_61, negated_conjecture, (r1_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,X1,X2),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))|~r1_binop_1(esk2_0,X2,esk6_0)|~r1_binop_1(esk1_0,X1,esk5_0)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_30]), c_0_26]), c_0_28])]), c_0_20])).
% 1.19/1.34  cnf(c_0_62, negated_conjecture, (~r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])])).
% 1.19/1.34  cnf(c_0_63, negated_conjecture, (r3_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k1_domain_1(esk1_0,esk2_0,X1,X2),k6_filter_1(esk1_0,esk2_0,esk5_0,esk6_0))|~r2_binop_1(esk2_0,X2,esk6_0)|~r2_binop_1(esk1_0,X1,esk5_0)|~r1_binop_1(esk2_0,X2,esk6_0)|~r1_binop_1(esk1_0,X1,esk5_0)|~m1_subset_1(k1_domain_1(esk1_0,esk2_0,X1,X2),k2_zfmisc_1(esk1_0,esk2_0))|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk1_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 1.19/1.34  cnf(c_0_64, negated_conjecture, (~r2_binop_1(esk2_0,esk4_0,esk6_0)|~r2_binop_1(esk1_0,esk3_0,esk5_0)|~r1_binop_1(esk2_0,esk4_0,esk6_0)|~r1_binop_1(esk1_0,esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_31]), c_0_12]), c_0_19])])).
% 1.19/1.34  cnf(c_0_65, negated_conjecture, (r2_binop_1(esk2_0,X1,esk6_0)|~r3_binop_1(esk2_0,X1,esk6_0)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_29]), c_0_25]), c_0_27])])).
% 1.19/1.34  cnf(c_0_66, negated_conjecture, (~r2_binop_1(esk1_0,esk3_0,esk5_0)|~r1_binop_1(esk2_0,esk4_0,esk6_0)|~r1_binop_1(esk1_0,esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_59]), c_0_12])])).
% 1.19/1.34  cnf(c_0_67, negated_conjecture, (r2_binop_1(esk1_0,X1,esk5_0)|~r3_binop_1(esk1_0,X1,esk5_0)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_30]), c_0_26]), c_0_28])])).
% 1.19/1.34  cnf(c_0_68, negated_conjecture, (~r1_binop_1(esk2_0,esk4_0,esk6_0)|~r1_binop_1(esk1_0,esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_51]), c_0_19])])).
% 1.19/1.34  cnf(c_0_69, negated_conjecture, (r1_binop_1(esk2_0,X1,esk6_0)|~r3_binop_1(esk2_0,X1,esk6_0)|~m1_subset_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_29]), c_0_25]), c_0_27])])).
% 1.19/1.34  cnf(c_0_70, negated_conjecture, (~r1_binop_1(esk1_0,esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_59]), c_0_12])])).
% 1.19/1.34  cnf(c_0_71, negated_conjecture, (r1_binop_1(esk1_0,X1,esk5_0)|~r3_binop_1(esk1_0,X1,esk5_0)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_30]), c_0_26]), c_0_28])])).
% 1.19/1.34  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_51]), c_0_19])]), ['proof']).
% 1.19/1.34  # SZS output end CNFRefutation
% 1.19/1.34  # Proof object total steps             : 73
% 1.19/1.34  # Proof object clause steps            : 60
% 1.19/1.34  # Proof object formula steps           : 13
% 1.19/1.34  # Proof object conjectures             : 47
% 1.19/1.34  # Proof object clause conjectures      : 44
% 1.19/1.34  # Proof object formula conjectures     : 3
% 1.19/1.34  # Proof object initial clauses used    : 26
% 1.19/1.34  # Proof object initial formulas used   : 6
% 1.19/1.34  # Proof object generating inferences   : 32
% 1.19/1.34  # Proof object simplifying inferences  : 151
% 1.19/1.34  # Training examples: 0 positive, 0 negative
% 1.19/1.34  # Parsed axioms                        : 6
% 1.19/1.34  # Removed by relevancy pruning/SinE    : 0
% 1.19/1.34  # Initial clauses                      : 26
% 1.19/1.34  # Removed in clause preprocessing      : 0
% 1.19/1.34  # Initial clauses in saturation        : 26
% 1.19/1.34  # Processed clauses                    : 872
% 1.19/1.34  # ...of these trivial                  : 0
% 1.19/1.34  # ...subsumed                          : 42
% 1.19/1.34  # ...remaining for further processing  : 830
% 1.19/1.34  # Other redundant clauses eliminated   : 0
% 1.19/1.34  # Clauses deleted for lack of memory   : 0
% 1.19/1.34  # Backward-subsumed                    : 50
% 1.19/1.34  # Backward-rewritten                   : 219
% 1.19/1.34  # Generated clauses                    : 54881
% 1.19/1.34  # ...of the previous two non-trivial   : 54870
% 1.19/1.34  # Contextual simplify-reflections      : 21
% 1.19/1.34  # Paramodulations                      : 54878
% 1.19/1.34  # Factorizations                       : 0
% 1.19/1.34  # Equation resolutions                 : 0
% 1.19/1.34  # Propositional unsat checks           : 0
% 1.19/1.34  #    Propositional check models        : 0
% 1.19/1.34  #    Propositional check unsatisfiable : 0
% 1.19/1.34  #    Propositional clauses             : 0
% 1.19/1.34  #    Propositional clauses after purity: 0
% 1.19/1.34  #    Propositional unsat core size     : 0
% 1.19/1.34  #    Propositional preprocessing time  : 0.000
% 1.19/1.34  #    Propositional encoding time       : 0.000
% 1.19/1.34  #    Propositional solver time         : 0.000
% 1.19/1.34  #    Success case prop preproc time    : 0.000
% 1.19/1.34  #    Success case prop encoding time   : 0.000
% 1.19/1.34  #    Success case prop solver time     : 0.000
% 1.19/1.34  # Current number of processed clauses  : 532
% 1.19/1.34  #    Positive orientable unit clauses  : 19
% 1.19/1.34  #    Positive unorientable unit clauses: 0
% 1.19/1.34  #    Negative unit clauses             : 4
% 1.19/1.34  #    Non-unit-clauses                  : 509
% 1.19/1.34  # Current number of unprocessed clauses: 54029
% 1.19/1.34  # ...number of literals in the above   : 358728
% 1.19/1.34  # Current number of archived formulas  : 0
% 1.19/1.34  # Current number of archived clauses   : 298
% 1.19/1.34  # Clause-clause subsumption calls (NU) : 101194
% 1.19/1.34  # Rec. Clause-clause subsumption calls : 5143
% 1.19/1.34  # Non-unit clause-clause subsumptions  : 113
% 1.19/1.34  # Unit Clause-clause subsumption calls : 646
% 1.19/1.34  # Rewrite failures with RHS unbound    : 0
% 1.19/1.34  # BW rewrite match attempts            : 3
% 1.19/1.34  # BW rewrite match successes           : 3
% 1.19/1.34  # Condensation attempts                : 0
% 1.19/1.34  # Condensation successes               : 0
% 1.19/1.34  # Termbank termtop insertions          : 5772837
% 1.19/1.34  
% 1.19/1.34  # -------------------------------------------------
% 1.19/1.34  # User time                : 0.954 s
% 1.19/1.34  # System time              : 0.046 s
% 1.19/1.34  # Total time               : 1.000 s
% 1.19/1.34  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
