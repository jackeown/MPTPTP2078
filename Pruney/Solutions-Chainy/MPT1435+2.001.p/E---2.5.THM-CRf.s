%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:52 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   93 (2820 expanded)
%              Number of clauses        :   82 ( 867 expanded)
%              Number of leaves         :    5 ( 712 expanded)
%              Depth                    :   18
%              Number of atoms          :  825 (39400 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal clause size      :   49 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_binop_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_filter_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_filter_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_filter_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_filter_1)).

fof(c_0_5,plain,(
    ! [X7,X8,X9] :
      ( ( r4_binop_1(X7,X8,X9)
        | ~ r6_binop_1(X7,X8,X9)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,k2_zfmisc_1(X7,X7),X7)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,X7),X7)))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,k2_zfmisc_1(X7,X7),X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,X7),X7))) )
      & ( r5_binop_1(X7,X8,X9)
        | ~ r6_binop_1(X7,X8,X9)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,k2_zfmisc_1(X7,X7),X7)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,X7),X7)))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,k2_zfmisc_1(X7,X7),X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,X7),X7))) )
      & ( ~ r4_binop_1(X7,X8,X9)
        | ~ r5_binop_1(X7,X8,X9)
        | r6_binop_1(X7,X8,X9)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,k2_zfmisc_1(X7,X7),X7)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,X7),X7)))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,k2_zfmisc_1(X7,X7),X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,X7),X7))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_binop_1])])])])).

fof(c_0_6,plain,(
    ! [X10,X11,X12,X13] :
      ( ( v1_funct_1(k6_filter_1(X10,X11,X12,X13))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,k2_zfmisc_1(X10,X10),X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X10,X10),X10)))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,k2_zfmisc_1(X11,X11),X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11))) )
      & ( v1_funct_2(k6_filter_1(X10,X11,X12,X13),k2_zfmisc_1(k2_zfmisc_1(X10,X11),k2_zfmisc_1(X10,X11)),k2_zfmisc_1(X10,X11))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,k2_zfmisc_1(X10,X10),X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X10,X10),X10)))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,k2_zfmisc_1(X11,X11),X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11))) )
      & ( m1_subset_1(k6_filter_1(X10,X11,X12,X13),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X10,X11),k2_zfmisc_1(X10,X11)),k2_zfmisc_1(X10,X11))))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,k2_zfmisc_1(X10,X10),X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X10,X10),X10)))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,k2_zfmisc_1(X11,X11),X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_filter_1])])])).

fof(c_0_7,negated_conjecture,(
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

cnf(c_0_8,plain,
    ( r4_binop_1(X1,X2,X3)
    | ~ r6_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( m1_subset_1(k6_filter_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v1_funct_1(k6_filter_1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v1_funct_2(k6_filter_1(X1,X2,X3,X4),k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_12,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( ~ r4_binop_1(X14,X16,X17)
        | ~ r4_binop_1(X15,X18,X19)
        | r4_binop_1(k2_zfmisc_1(X14,X15),k6_filter_1(X14,X15,X16,X18),k6_filter_1(X14,X15,X17,X19))
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X14,X14),X14)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14)))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,k2_zfmisc_1(X14,X14),X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14)))
        | v1_xboole_0(X15)
        | v1_xboole_0(X14) )
      & ( r4_binop_1(X14,X16,X17)
        | ~ r4_binop_1(k2_zfmisc_1(X14,X15),k6_filter_1(X14,X15,X16,X18),k6_filter_1(X14,X15,X17,X19))
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X14,X14),X14)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14)))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,k2_zfmisc_1(X14,X14),X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14)))
        | v1_xboole_0(X15)
        | v1_xboole_0(X14) )
      & ( r4_binop_1(X15,X18,X19)
        | ~ r4_binop_1(k2_zfmisc_1(X14,X15),k6_filter_1(X14,X15,X16,X18),k6_filter_1(X14,X15,X17,X19))
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X14,X14),X14)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14)))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,k2_zfmisc_1(X14,X14),X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14)))
        | v1_xboole_0(X15)
        | v1_xboole_0(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t28_filter_1])])])])])).

fof(c_0_13,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).

cnf(c_0_14,plain,
    ( r4_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))
    | ~ r6_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))
    | ~ v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_15,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_2(esk4_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( r4_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6))
    | ~ r6_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( v1_xboole_0(X1)
    | r4_binop_1(k2_zfmisc_1(X1,esk1_0),k6_filter_1(X1,esk1_0,X2,X3),k6_filter_1(X1,esk1_0,X4,esk4_0))
    | ~ r4_binop_1(esk1_0,X3,esk4_0)
    | ~ r4_binop_1(X1,X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_2(esk3_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r4_binop_1(X1,X3,X4)
    | ~ r6_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X5),k6_filter_1(X1,X2,X4,X6))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r6_binop_1(esk1_0,esk3_0,esk4_0)
    | r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk6_0,k2_zfmisc_1(esk2_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_2(esk5_0,k2_zfmisc_1(esk2_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( v1_xboole_0(X1)
    | r4_binop_1(k2_zfmisc_1(X1,esk1_0),k6_filter_1(X1,esk1_0,X2,esk3_0),k6_filter_1(X1,esk1_0,X3,esk4_0))
    | ~ r4_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r4_binop_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_36,negated_conjecture,
    ( r4_binop_1(esk1_0,X1,esk4_0)
    | ~ r6_binop_1(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_37,plain,
    ( r5_binop_1(X1,X2,X3)
    | ~ r6_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_38,negated_conjecture,
    ( r4_binop_1(esk1_0,esk3_0,esk4_0)
    | r6_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_16]),c_0_23]),c_0_30]),c_0_31]),c_0_17]),c_0_24]),c_0_32]),c_0_33]),c_0_18]),c_0_25])]),c_0_19]),c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( v1_xboole_0(X1)
    | r4_binop_1(k2_zfmisc_1(X1,esk1_0),k6_filter_1(X1,esk1_0,X2,esk3_0),k6_filter_1(X1,esk1_0,X3,esk4_0))
    | ~ r4_binop_1(X1,X2,X3)
    | ~ r6_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_23]),c_0_24]),c_0_25])])).

fof(c_0_40,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r5_binop_1(X20,X22,X23)
        | ~ r5_binop_1(X21,X24,X25)
        | r5_binop_1(k2_zfmisc_1(X20,X21),k6_filter_1(X20,X21,X22,X24),k6_filter_1(X20,X21,X23,X25))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,k2_zfmisc_1(X21,X21),X21)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X21,X21),X21)))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,k2_zfmisc_1(X21,X21),X21)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X21,X21),X21)))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,k2_zfmisc_1(X20,X20),X20)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X20),X20)))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,k2_zfmisc_1(X20,X20),X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X20),X20)))
        | v1_xboole_0(X21)
        | v1_xboole_0(X20) )
      & ( r5_binop_1(X20,X22,X23)
        | ~ r5_binop_1(k2_zfmisc_1(X20,X21),k6_filter_1(X20,X21,X22,X24),k6_filter_1(X20,X21,X23,X25))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,k2_zfmisc_1(X21,X21),X21)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X21,X21),X21)))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,k2_zfmisc_1(X21,X21),X21)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X21,X21),X21)))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,k2_zfmisc_1(X20,X20),X20)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X20),X20)))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,k2_zfmisc_1(X20,X20),X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X20),X20)))
        | v1_xboole_0(X21)
        | v1_xboole_0(X20) )
      & ( r5_binop_1(X21,X24,X25)
        | ~ r5_binop_1(k2_zfmisc_1(X20,X21),k6_filter_1(X20,X21,X22,X24),k6_filter_1(X20,X21,X23,X25))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,k2_zfmisc_1(X21,X21),X21)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X21,X21),X21)))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,k2_zfmisc_1(X21,X21),X21)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X21,X21),X21)))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,k2_zfmisc_1(X20,X20),X20)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X20),X20)))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,k2_zfmisc_1(X20,X20),X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X20),X20)))
        | v1_xboole_0(X21)
        | v1_xboole_0(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_filter_1])])])])])).

cnf(c_0_41,plain,
    ( r5_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))
    | ~ r6_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))
    | ~ v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_42,negated_conjecture,
    ( v1_xboole_0(X1)
    | r4_binop_1(k2_zfmisc_1(X1,esk1_0),k6_filter_1(X1,esk1_0,X2,esk3_0),k6_filter_1(X1,esk1_0,X3,esk4_0))
    | ~ r4_binop_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_38]),c_0_39])).

cnf(c_0_43,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,plain,
    ( r5_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6))
    | ~ r6_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_45,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( r4_binop_1(k2_zfmisc_1(esk2_0,esk1_0),k6_filter_1(esk2_0,esk1_0,X1,esk3_0),k6_filter_1(esk2_0,esk1_0,esk6_0,esk4_0))
    | ~ r4_binop_1(esk2_0,X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_28]),c_0_30]),c_0_32])]),c_0_34])).

cnf(c_0_47,plain,
    ( r6_binop_1(X1,X2,X3)
    | ~ r4_binop_1(X1,X2,X3)
    | ~ r5_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r5_binop_1(X1,X3,X4)
    | ~ r6_binop_1(k2_zfmisc_1(X2,X1),k6_filter_1(X2,X1,X5,X3),k6_filter_1(X2,X1,X6,X4))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r6_binop_1(esk2_0,esk5_0,esk6_0)
    | r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r4_binop_1(X1,X3,X4)
    | ~ r6_binop_1(k2_zfmisc_1(X2,X1),k6_filter_1(X2,X1,X5,X3),k6_filter_1(X2,X1,X6,X4))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3) ),
    inference(spm,[status(thm)],[c_0_45,c_0_21])).

cnf(c_0_51,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( r4_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r4_binop_1(esk2_0,X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_28]),c_0_16]),c_0_23]),c_0_30]),c_0_17]),c_0_24]),c_0_32]),c_0_18]),c_0_25])]),c_0_34]),c_0_19])).

cnf(c_0_54,negated_conjecture,
    ( r4_binop_1(esk2_0,X1,esk6_0)
    | ~ r6_binop_1(esk2_0,X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_28]),c_0_30]),c_0_32])])).

cnf(c_0_55,negated_conjecture,
    ( r6_binop_1(esk2_0,X1,esk6_0)
    | ~ r5_binop_1(esk2_0,X1,esk6_0)
    | ~ r4_binop_1(esk2_0,X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_28]),c_0_30]),c_0_32])])).

cnf(c_0_56,negated_conjecture,
    ( r5_binop_1(esk2_0,esk5_0,esk6_0)
    | r6_binop_1(esk2_0,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_16]),c_0_23]),c_0_28]),c_0_29]),c_0_17]),c_0_24]),c_0_30]),c_0_31]),c_0_18]),c_0_25]),c_0_32]),c_0_33])]),c_0_34]),c_0_19])).

cnf(c_0_57,negated_conjecture,
    ( r4_binop_1(esk2_0,esk5_0,esk6_0)
    | r6_binop_1(esk2_0,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_49]),c_0_16]),c_0_23]),c_0_28]),c_0_29]),c_0_17]),c_0_24]),c_0_30]),c_0_31]),c_0_18]),c_0_25]),c_0_32]),c_0_33])]),c_0_34]),c_0_19])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(X1)
    | r5_binop_1(k2_zfmisc_1(X1,esk1_0),k6_filter_1(X1,esk1_0,X2,X3),k6_filter_1(X1,esk1_0,X4,esk4_0))
    | ~ r5_binop_1(esk1_0,X3,esk4_0)
    | ~ r5_binop_1(X1,X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r5_binop_1(X1,X3,X4)
    | ~ r6_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X5),k6_filter_1(X1,X2,X4,X6))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_44])).

cnf(c_0_60,negated_conjecture,
    ( r4_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r6_binop_1(esk2_0,X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r6_binop_1(esk2_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_29]),c_0_31]),c_0_33])]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(X1)
    | r5_binop_1(k2_zfmisc_1(X1,esk2_0),k6_filter_1(X1,esk2_0,X2,X3),k6_filter_1(X1,esk2_0,X4,esk6_0))
    | ~ r5_binop_1(esk2_0,X3,esk6_0)
    | ~ r5_binop_1(X1,X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_28]),c_0_30]),c_0_32])]),c_0_34])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(X1)
    | r5_binop_1(k2_zfmisc_1(X1,esk1_0),k6_filter_1(X1,esk1_0,X2,esk3_0),k6_filter_1(X1,esk1_0,X3,esk4_0))
    | ~ r5_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r5_binop_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_64,negated_conjecture,
    ( r5_binop_1(esk1_0,X1,esk4_0)
    | ~ r6_binop_1(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_65,negated_conjecture,
    ( r6_binop_1(esk1_0,X1,esk4_0)
    | ~ r5_binop_1(esk1_0,X1,esk4_0)
    | ~ r4_binop_1(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_66,negated_conjecture,
    ( r5_binop_1(esk1_0,esk3_0,esk4_0)
    | r6_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_27]),c_0_28]),c_0_29]),c_0_16]),c_0_23]),c_0_30]),c_0_31]),c_0_17]),c_0_24]),c_0_32]),c_0_33]),c_0_18]),c_0_25])]),c_0_19]),c_0_34])).

cnf(c_0_67,negated_conjecture,
    ( r4_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_29]),c_0_61]),c_0_31]),c_0_33])])).

cnf(c_0_68,negated_conjecture,
    ( v1_xboole_0(X1)
    | r5_binop_1(k2_zfmisc_1(X1,esk2_0),k6_filter_1(X1,esk2_0,X2,esk5_0),k6_filter_1(X1,esk2_0,X3,esk6_0))
    | ~ r5_binop_1(esk2_0,esk5_0,esk6_0)
    | ~ r5_binop_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_29]),c_0_31]),c_0_33])])).

cnf(c_0_69,negated_conjecture,
    ( r5_binop_1(esk2_0,X1,esk6_0)
    | ~ r6_binop_1(esk2_0,X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_28]),c_0_30]),c_0_32])])).

cnf(c_0_70,negated_conjecture,
    ( v1_xboole_0(X1)
    | r4_binop_1(k2_zfmisc_1(X1,esk2_0),k6_filter_1(X1,esk2_0,X2,X3),k6_filter_1(X1,esk2_0,X4,esk6_0))
    | ~ r4_binop_1(esk2_0,X3,esk6_0)
    | ~ r4_binop_1(X1,X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_28]),c_0_30]),c_0_32])]),c_0_34])).

cnf(c_0_71,negated_conjecture,
    ( v1_xboole_0(X1)
    | r5_binop_1(k2_zfmisc_1(X1,esk1_0),k6_filter_1(X1,esk1_0,X2,esk3_0),k6_filter_1(X1,esk1_0,X3,esk4_0))
    | ~ r5_binop_1(X1,X2,X3)
    | ~ r6_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_72,negated_conjecture,
    ( r6_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_73,negated_conjecture,
    ( v1_xboole_0(X1)
    | r5_binop_1(k2_zfmisc_1(X1,esk2_0),k6_filter_1(X1,esk2_0,X2,esk5_0),k6_filter_1(X1,esk2_0,X3,esk6_0))
    | ~ r5_binop_1(X1,X2,X3)
    | ~ r6_binop_1(esk2_0,esk5_0,esk6_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_29]),c_0_31]),c_0_33])])).

cnf(c_0_74,negated_conjecture,
    ( v1_xboole_0(X1)
    | r4_binop_1(k2_zfmisc_1(X1,esk2_0),k6_filter_1(X1,esk2_0,X2,esk5_0),k6_filter_1(X1,esk2_0,X3,esk6_0))
    | ~ r4_binop_1(esk2_0,esk5_0,esk6_0)
    | ~ r4_binop_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_29]),c_0_31]),c_0_33])])).

cnf(c_0_75,negated_conjecture,
    ( v1_xboole_0(X1)
    | r5_binop_1(k2_zfmisc_1(X1,esk1_0),k6_filter_1(X1,esk1_0,X2,esk3_0),k6_filter_1(X1,esk1_0,X3,esk4_0))
    | ~ r5_binop_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72])])).

cnf(c_0_76,plain,
    ( r6_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))
    | ~ r5_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))
    | ~ r4_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))
    | ~ v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_77,negated_conjecture,
    ( v1_xboole_0(X1)
    | r5_binop_1(k2_zfmisc_1(X1,esk2_0),k6_filter_1(X1,esk2_0,X2,esk5_0),k6_filter_1(X1,esk2_0,X3,esk6_0))
    | ~ r5_binop_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_61])])).

cnf(c_0_78,negated_conjecture,
    ( v1_xboole_0(X1)
    | r4_binop_1(k2_zfmisc_1(X1,esk2_0),k6_filter_1(X1,esk2_0,X2,esk5_0),k6_filter_1(X1,esk2_0,X3,esk6_0))
    | ~ r4_binop_1(X1,X2,X3)
    | ~ r6_binop_1(esk2_0,esk5_0,esk6_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_54]),c_0_29]),c_0_31]),c_0_33])])).

cnf(c_0_79,negated_conjecture,
    ( r5_binop_1(k2_zfmisc_1(esk2_0,esk1_0),k6_filter_1(esk2_0,esk1_0,X1,esk3_0),k6_filter_1(esk2_0,esk1_0,esk6_0,esk4_0))
    | ~ r5_binop_1(esk2_0,X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_28]),c_0_30]),c_0_32])]),c_0_34])).

cnf(c_0_80,negated_conjecture,
    ( ~ r6_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r6_binop_1(esk2_0,esk5_0,esk6_0)
    | ~ r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_81,plain,
    ( r6_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6))
    | ~ r5_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6))
    | ~ r4_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_82,negated_conjecture,
    ( r5_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,X1,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | ~ r5_binop_1(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_83,negated_conjecture,
    ( v1_xboole_0(X1)
    | r4_binop_1(k2_zfmisc_1(X1,esk2_0),k6_filter_1(X1,esk2_0,X2,esk5_0),k6_filter_1(X1,esk2_0,X3,esk6_0))
    | ~ r4_binop_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_57]),c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( r5_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r5_binop_1(esk2_0,X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_79]),c_0_28]),c_0_16]),c_0_23]),c_0_30]),c_0_17]),c_0_24]),c_0_32]),c_0_18]),c_0_25])]),c_0_34]),c_0_19])).

cnf(c_0_85,negated_conjecture,
    ( ~ r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | ~ r6_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_61])])).

cnf(c_0_86,negated_conjecture,
    ( r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,X1,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | ~ r5_binop_1(esk1_0,X1,esk4_0)
    | ~ r4_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,X1,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_28]),c_0_16]),c_0_29]),c_0_30]),c_0_17]),c_0_31]),c_0_32]),c_0_18]),c_0_33])])).

cnf(c_0_87,negated_conjecture,
    ( r4_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,X1,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | ~ r4_binop_1(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_88,negated_conjecture,
    ( r5_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r6_binop_1(esk2_0,X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_69])).

cnf(c_0_89,negated_conjecture,
    ( ~ r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_72])])).

cnf(c_0_90,negated_conjecture,
    ( r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,X1,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))
    | ~ r5_binop_1(esk1_0,X1,esk4_0)
    | ~ r4_binop_1(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( r5_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_29]),c_0_61]),c_0_31]),c_0_33])])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91]),c_0_67]),c_0_23]),c_0_24]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:58:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.46  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.46  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.46  #
% 0.18/0.46  # Preprocessing time       : 0.029 s
% 0.18/0.46  # Presaturation interreduction done
% 0.18/0.46  
% 0.18/0.46  # Proof found!
% 0.18/0.46  # SZS status Theorem
% 0.18/0.46  # SZS output start CNFRefutation
% 0.18/0.46  fof(d11_binop_1, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>(r6_binop_1(X1,X2,X3)<=>(r4_binop_1(X1,X2,X3)&r5_binop_1(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_binop_1)).
% 0.18/0.46  fof(dt_k6_filter_1, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))&v1_funct_1(X4))&v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))))=>((v1_funct_1(k6_filter_1(X1,X2,X3,X4))&v1_funct_2(k6_filter_1(X1,X2,X3,X4),k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2)))&m1_subset_1(k6_filter_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_filter_1)).
% 0.18/0.46  fof(t30_filter_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))))=>((r6_binop_1(X1,X3,X4)&r6_binop_1(X2,X5,X6))<=>r6_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X5),k6_filter_1(X1,X2,X4,X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_filter_1)).
% 0.18/0.46  fof(t28_filter_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))))=>((r4_binop_1(X1,X3,X4)&r4_binop_1(X2,X5,X6))<=>r4_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X5),k6_filter_1(X1,X2,X4,X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_filter_1)).
% 0.18/0.46  fof(t29_filter_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))))=>((r5_binop_1(X1,X3,X4)&r5_binop_1(X2,X5,X6))<=>r5_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X5),k6_filter_1(X1,X2,X4,X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_filter_1)).
% 0.18/0.46  fof(c_0_5, plain, ![X7, X8, X9]:(((r4_binop_1(X7,X8,X9)|~r6_binop_1(X7,X8,X9)|(~v1_funct_1(X9)|~v1_funct_2(X9,k2_zfmisc_1(X7,X7),X7)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,X7),X7))))|(~v1_funct_1(X8)|~v1_funct_2(X8,k2_zfmisc_1(X7,X7),X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,X7),X7)))))&(r5_binop_1(X7,X8,X9)|~r6_binop_1(X7,X8,X9)|(~v1_funct_1(X9)|~v1_funct_2(X9,k2_zfmisc_1(X7,X7),X7)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,X7),X7))))|(~v1_funct_1(X8)|~v1_funct_2(X8,k2_zfmisc_1(X7,X7),X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,X7),X7))))))&(~r4_binop_1(X7,X8,X9)|~r5_binop_1(X7,X8,X9)|r6_binop_1(X7,X8,X9)|(~v1_funct_1(X9)|~v1_funct_2(X9,k2_zfmisc_1(X7,X7),X7)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,X7),X7))))|(~v1_funct_1(X8)|~v1_funct_2(X8,k2_zfmisc_1(X7,X7),X7)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,X7),X7)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_binop_1])])])])).
% 0.18/0.46  fof(c_0_6, plain, ![X10, X11, X12, X13]:(((v1_funct_1(k6_filter_1(X10,X11,X12,X13))|(~v1_funct_1(X12)|~v1_funct_2(X12,k2_zfmisc_1(X10,X10),X10)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X10,X10),X10)))|~v1_funct_1(X13)|~v1_funct_2(X13,k2_zfmisc_1(X11,X11),X11)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11)))))&(v1_funct_2(k6_filter_1(X10,X11,X12,X13),k2_zfmisc_1(k2_zfmisc_1(X10,X11),k2_zfmisc_1(X10,X11)),k2_zfmisc_1(X10,X11))|(~v1_funct_1(X12)|~v1_funct_2(X12,k2_zfmisc_1(X10,X10),X10)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X10,X10),X10)))|~v1_funct_1(X13)|~v1_funct_2(X13,k2_zfmisc_1(X11,X11),X11)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11))))))&(m1_subset_1(k6_filter_1(X10,X11,X12,X13),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X10,X11),k2_zfmisc_1(X10,X11)),k2_zfmisc_1(X10,X11))))|(~v1_funct_1(X12)|~v1_funct_2(X12,k2_zfmisc_1(X10,X10),X10)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X10,X10),X10)))|~v1_funct_1(X13)|~v1_funct_2(X13,k2_zfmisc_1(X11,X11),X11)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_filter_1])])])).
% 0.18/0.46  fof(c_0_7, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))))=>((r6_binop_1(X1,X3,X4)&r6_binop_1(X2,X5,X6))<=>r6_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X5),k6_filter_1(X1,X2,X4,X6)))))))))), inference(assume_negation,[status(cth)],[t30_filter_1])).
% 0.18/0.46  cnf(c_0_8, plain, (r4_binop_1(X1,X2,X3)|~r6_binop_1(X1,X2,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.18/0.46  cnf(c_0_9, plain, (m1_subset_1(k6_filter_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X4)|~v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.46  cnf(c_0_10, plain, (v1_funct_1(k6_filter_1(X1,X2,X3,X4))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X4)|~v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.46  cnf(c_0_11, plain, (v1_funct_2(k6_filter_1(X1,X2,X3,X4),k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X4)|~v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.46  fof(c_0_12, plain, ![X14, X15, X16, X17, X18, X19]:((~r4_binop_1(X14,X16,X17)|~r4_binop_1(X15,X18,X19)|r4_binop_1(k2_zfmisc_1(X14,X15),k6_filter_1(X14,X15,X16,X18),k6_filter_1(X14,X15,X17,X19))|(~v1_funct_1(X19)|~v1_funct_2(X19,k2_zfmisc_1(X15,X15),X15)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15))))|(~v1_funct_1(X18)|~v1_funct_2(X18,k2_zfmisc_1(X15,X15),X15)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15))))|(~v1_funct_1(X17)|~v1_funct_2(X17,k2_zfmisc_1(X14,X14),X14)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14))))|(~v1_funct_1(X16)|~v1_funct_2(X16,k2_zfmisc_1(X14,X14),X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14))))|v1_xboole_0(X15)|v1_xboole_0(X14))&((r4_binop_1(X14,X16,X17)|~r4_binop_1(k2_zfmisc_1(X14,X15),k6_filter_1(X14,X15,X16,X18),k6_filter_1(X14,X15,X17,X19))|(~v1_funct_1(X19)|~v1_funct_2(X19,k2_zfmisc_1(X15,X15),X15)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15))))|(~v1_funct_1(X18)|~v1_funct_2(X18,k2_zfmisc_1(X15,X15),X15)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15))))|(~v1_funct_1(X17)|~v1_funct_2(X17,k2_zfmisc_1(X14,X14),X14)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14))))|(~v1_funct_1(X16)|~v1_funct_2(X16,k2_zfmisc_1(X14,X14),X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14))))|v1_xboole_0(X15)|v1_xboole_0(X14))&(r4_binop_1(X15,X18,X19)|~r4_binop_1(k2_zfmisc_1(X14,X15),k6_filter_1(X14,X15,X16,X18),k6_filter_1(X14,X15,X17,X19))|(~v1_funct_1(X19)|~v1_funct_2(X19,k2_zfmisc_1(X15,X15),X15)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15))))|(~v1_funct_1(X18)|~v1_funct_2(X18,k2_zfmisc_1(X15,X15),X15)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15))))|(~v1_funct_1(X17)|~v1_funct_2(X17,k2_zfmisc_1(X14,X14),X14)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14))))|(~v1_funct_1(X16)|~v1_funct_2(X16,k2_zfmisc_1(X14,X14),X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14))))|v1_xboole_0(X15)|v1_xboole_0(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t28_filter_1])])])])])).
% 0.18/0.46  fof(c_0_13, negated_conjecture, (~v1_xboole_0(esk1_0)&(~v1_xboole_0(esk2_0)&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,k2_zfmisc_1(esk2_0,esk2_0),esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,k2_zfmisc_1(esk2_0,esk2_0),esk2_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0))))&((~r6_binop_1(esk1_0,esk3_0,esk4_0)|~r6_binop_1(esk2_0,esk5_0,esk6_0)|~r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0)))&((r6_binop_1(esk1_0,esk3_0,esk4_0)|r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0)))&(r6_binop_1(esk2_0,esk5_0,esk6_0)|r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).
% 0.18/0.46  cnf(c_0_14, plain, (r4_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))|~r6_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))|~v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X5)|~v1_funct_1(X4)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), c_0_11])).
% 0.18/0.46  cnf(c_0_15, plain, (r4_binop_1(k2_zfmisc_1(X1,X4),k6_filter_1(X1,X4,X2,X5),k6_filter_1(X1,X4,X3,X6))|v1_xboole_0(X4)|v1_xboole_0(X1)|~r4_binop_1(X1,X2,X3)|~r4_binop_1(X4,X5,X6)|~v1_funct_1(X6)|~v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))|~v1_funct_1(X5)|~v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.46  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  cnf(c_0_17, negated_conjecture, (v1_funct_2(esk4_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  cnf(c_0_19, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  cnf(c_0_20, plain, (r4_binop_1(X1,X2,X3)|v1_xboole_0(X4)|v1_xboole_0(X1)|~r4_binop_1(k2_zfmisc_1(X1,X4),k6_filter_1(X1,X4,X2,X5),k6_filter_1(X1,X4,X3,X6))|~v1_funct_1(X6)|~v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))|~v1_funct_1(X5)|~v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.46  cnf(c_0_21, plain, (r4_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6))|~r6_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X6)|~v1_funct_1(X5)|~v1_funct_1(X4)|~v1_funct_1(X3)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_9]), c_0_10]), c_0_11])).
% 0.18/0.46  cnf(c_0_22, negated_conjecture, (v1_xboole_0(X1)|r4_binop_1(k2_zfmisc_1(X1,esk1_0),k6_filter_1(X1,esk1_0,X2,X3),k6_filter_1(X1,esk1_0,X4,esk4_0))|~r4_binop_1(esk1_0,X3,esk4_0)|~r4_binop_1(X1,X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)|~v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X4)|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.18/0.46  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  cnf(c_0_24, negated_conjecture, (v1_funct_2(esk3_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  cnf(c_0_26, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r4_binop_1(X1,X3,X4)|~r6_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X5),k6_filter_1(X1,X2,X4,X6))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X6)|~v1_funct_1(X5)|~v1_funct_1(X4)|~v1_funct_1(X3)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.18/0.46  cnf(c_0_27, negated_conjecture, (r6_binop_1(esk1_0,esk3_0,esk4_0)|r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  cnf(c_0_30, negated_conjecture, (v1_funct_2(esk6_0,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  cnf(c_0_31, negated_conjecture, (v1_funct_2(esk5_0,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  cnf(c_0_34, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  cnf(c_0_35, negated_conjecture, (v1_xboole_0(X1)|r4_binop_1(k2_zfmisc_1(X1,esk1_0),k6_filter_1(X1,esk1_0,X2,esk3_0),k6_filter_1(X1,esk1_0,X3,esk4_0))|~r4_binop_1(esk1_0,esk3_0,esk4_0)|~r4_binop_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])])).
% 0.18/0.46  cnf(c_0_36, negated_conjecture, (r4_binop_1(esk1_0,X1,esk4_0)|~r6_binop_1(esk1_0,X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))|~v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_16]), c_0_17]), c_0_18])])).
% 0.18/0.46  cnf(c_0_37, plain, (r5_binop_1(X1,X2,X3)|~r6_binop_1(X1,X2,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.18/0.46  cnf(c_0_38, negated_conjecture, (r4_binop_1(esk1_0,esk3_0,esk4_0)|r6_binop_1(esk1_0,esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_16]), c_0_23]), c_0_30]), c_0_31]), c_0_17]), c_0_24]), c_0_32]), c_0_33]), c_0_18]), c_0_25])]), c_0_19]), c_0_34])).
% 0.18/0.46  cnf(c_0_39, negated_conjecture, (v1_xboole_0(X1)|r4_binop_1(k2_zfmisc_1(X1,esk1_0),k6_filter_1(X1,esk1_0,X2,esk3_0),k6_filter_1(X1,esk1_0,X3,esk4_0))|~r4_binop_1(X1,X2,X3)|~r6_binop_1(esk1_0,esk3_0,esk4_0)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_23]), c_0_24]), c_0_25])])).
% 0.18/0.46  fof(c_0_40, plain, ![X20, X21, X22, X23, X24, X25]:((~r5_binop_1(X20,X22,X23)|~r5_binop_1(X21,X24,X25)|r5_binop_1(k2_zfmisc_1(X20,X21),k6_filter_1(X20,X21,X22,X24),k6_filter_1(X20,X21,X23,X25))|(~v1_funct_1(X25)|~v1_funct_2(X25,k2_zfmisc_1(X21,X21),X21)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X21,X21),X21))))|(~v1_funct_1(X24)|~v1_funct_2(X24,k2_zfmisc_1(X21,X21),X21)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X21,X21),X21))))|(~v1_funct_1(X23)|~v1_funct_2(X23,k2_zfmisc_1(X20,X20),X20)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X20),X20))))|(~v1_funct_1(X22)|~v1_funct_2(X22,k2_zfmisc_1(X20,X20),X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X20),X20))))|v1_xboole_0(X21)|v1_xboole_0(X20))&((r5_binop_1(X20,X22,X23)|~r5_binop_1(k2_zfmisc_1(X20,X21),k6_filter_1(X20,X21,X22,X24),k6_filter_1(X20,X21,X23,X25))|(~v1_funct_1(X25)|~v1_funct_2(X25,k2_zfmisc_1(X21,X21),X21)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X21,X21),X21))))|(~v1_funct_1(X24)|~v1_funct_2(X24,k2_zfmisc_1(X21,X21),X21)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X21,X21),X21))))|(~v1_funct_1(X23)|~v1_funct_2(X23,k2_zfmisc_1(X20,X20),X20)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X20),X20))))|(~v1_funct_1(X22)|~v1_funct_2(X22,k2_zfmisc_1(X20,X20),X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X20),X20))))|v1_xboole_0(X21)|v1_xboole_0(X20))&(r5_binop_1(X21,X24,X25)|~r5_binop_1(k2_zfmisc_1(X20,X21),k6_filter_1(X20,X21,X22,X24),k6_filter_1(X20,X21,X23,X25))|(~v1_funct_1(X25)|~v1_funct_2(X25,k2_zfmisc_1(X21,X21),X21)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X21,X21),X21))))|(~v1_funct_1(X24)|~v1_funct_2(X24,k2_zfmisc_1(X21,X21),X21)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X21,X21),X21))))|(~v1_funct_1(X23)|~v1_funct_2(X23,k2_zfmisc_1(X20,X20),X20)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X20),X20))))|(~v1_funct_1(X22)|~v1_funct_2(X22,k2_zfmisc_1(X20,X20),X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X20,X20),X20))))|v1_xboole_0(X21)|v1_xboole_0(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t29_filter_1])])])])])).
% 0.18/0.46  cnf(c_0_41, plain, (r5_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))|~r6_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))|~v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X5)|~v1_funct_1(X4)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_9]), c_0_10]), c_0_11])).
% 0.18/0.46  cnf(c_0_42, negated_conjecture, (v1_xboole_0(X1)|r4_binop_1(k2_zfmisc_1(X1,esk1_0),k6_filter_1(X1,esk1_0,X2,esk3_0),k6_filter_1(X1,esk1_0,X3,esk4_0))|~r4_binop_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_38]), c_0_39])).
% 0.18/0.46  cnf(c_0_43, plain, (r5_binop_1(X1,X2,X3)|v1_xboole_0(X1)|v1_xboole_0(X4)|~r5_binop_1(k2_zfmisc_1(X4,X1),k6_filter_1(X4,X1,X5,X2),k6_filter_1(X4,X1,X6,X3))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X6)|~v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))|~v1_funct_1(X5)|~v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.18/0.46  cnf(c_0_44, plain, (r5_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6))|~r6_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X6)|~v1_funct_1(X5)|~v1_funct_1(X4)|~v1_funct_1(X3)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_9]), c_0_10]), c_0_11])).
% 0.18/0.46  cnf(c_0_45, plain, (r4_binop_1(X1,X2,X3)|v1_xboole_0(X1)|v1_xboole_0(X4)|~r4_binop_1(k2_zfmisc_1(X4,X1),k6_filter_1(X4,X1,X5,X2),k6_filter_1(X4,X1,X6,X3))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X6)|~v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))|~v1_funct_1(X5)|~v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.46  cnf(c_0_46, negated_conjecture, (r4_binop_1(k2_zfmisc_1(esk2_0,esk1_0),k6_filter_1(esk2_0,esk1_0,X1,esk3_0),k6_filter_1(esk2_0,esk1_0,esk6_0,esk4_0))|~r4_binop_1(esk2_0,X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))|~v1_funct_2(X1,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)|~v1_funct_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_28]), c_0_30]), c_0_32])]), c_0_34])).
% 0.18/0.46  cnf(c_0_47, plain, (r6_binop_1(X1,X2,X3)|~r4_binop_1(X1,X2,X3)|~r5_binop_1(X1,X2,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.18/0.46  cnf(c_0_48, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r5_binop_1(X1,X3,X4)|~r6_binop_1(k2_zfmisc_1(X2,X1),k6_filter_1(X2,X1,X5,X3),k6_filter_1(X2,X1,X6,X4))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X6)|~v1_funct_1(X5)|~v1_funct_1(X4)|~v1_funct_1(X3)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.18/0.46  cnf(c_0_49, negated_conjecture, (r6_binop_1(esk2_0,esk5_0,esk6_0)|r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  cnf(c_0_50, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r4_binop_1(X1,X3,X4)|~r6_binop_1(k2_zfmisc_1(X2,X1),k6_filter_1(X2,X1,X5,X3),k6_filter_1(X2,X1,X6,X4))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X6)|~v1_funct_1(X5)|~v1_funct_1(X4)|~v1_funct_1(X3)), inference(spm,[status(thm)],[c_0_45, c_0_21])).
% 0.18/0.46  cnf(c_0_51, plain, (r5_binop_1(k2_zfmisc_1(X1,X4),k6_filter_1(X1,X4,X2,X5),k6_filter_1(X1,X4,X3,X6))|v1_xboole_0(X4)|v1_xboole_0(X1)|~r5_binop_1(X1,X2,X3)|~r5_binop_1(X4,X5,X6)|~v1_funct_1(X6)|~v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))|~v1_funct_1(X5)|~v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.18/0.46  cnf(c_0_52, plain, (r5_binop_1(X1,X2,X3)|v1_xboole_0(X4)|v1_xboole_0(X1)|~r5_binop_1(k2_zfmisc_1(X1,X4),k6_filter_1(X1,X4,X2,X5),k6_filter_1(X1,X4,X3,X6))|~v1_funct_1(X6)|~v1_funct_2(X6,k2_zfmisc_1(X4,X4),X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))|~v1_funct_1(X5)|~v1_funct_2(X5,k2_zfmisc_1(X4,X4),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.18/0.46  cnf(c_0_53, negated_conjecture, (r4_binop_1(esk1_0,esk3_0,esk4_0)|~r4_binop_1(esk2_0,X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))|~v1_funct_2(X1,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)|~v1_funct_1(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_28]), c_0_16]), c_0_23]), c_0_30]), c_0_17]), c_0_24]), c_0_32]), c_0_18]), c_0_25])]), c_0_34]), c_0_19])).
% 0.18/0.46  cnf(c_0_54, negated_conjecture, (r4_binop_1(esk2_0,X1,esk6_0)|~r6_binop_1(esk2_0,X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))|~v1_funct_2(X1,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_28]), c_0_30]), c_0_32])])).
% 0.18/0.46  cnf(c_0_55, negated_conjecture, (r6_binop_1(esk2_0,X1,esk6_0)|~r5_binop_1(esk2_0,X1,esk6_0)|~r4_binop_1(esk2_0,X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))|~v1_funct_2(X1,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_28]), c_0_30]), c_0_32])])).
% 0.18/0.46  cnf(c_0_56, negated_conjecture, (r5_binop_1(esk2_0,esk5_0,esk6_0)|r6_binop_1(esk2_0,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_16]), c_0_23]), c_0_28]), c_0_29]), c_0_17]), c_0_24]), c_0_30]), c_0_31]), c_0_18]), c_0_25]), c_0_32]), c_0_33])]), c_0_34]), c_0_19])).
% 0.18/0.46  cnf(c_0_57, negated_conjecture, (r4_binop_1(esk2_0,esk5_0,esk6_0)|r6_binop_1(esk2_0,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_49]), c_0_16]), c_0_23]), c_0_28]), c_0_29]), c_0_17]), c_0_24]), c_0_30]), c_0_31]), c_0_18]), c_0_25]), c_0_32]), c_0_33])]), c_0_34]), c_0_19])).
% 0.18/0.46  cnf(c_0_58, negated_conjecture, (v1_xboole_0(X1)|r5_binop_1(k2_zfmisc_1(X1,esk1_0),k6_filter_1(X1,esk1_0,X2,X3),k6_filter_1(X1,esk1_0,X4,esk4_0))|~r5_binop_1(esk1_0,X3,esk4_0)|~r5_binop_1(X1,X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)|~v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X4)|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.18/0.46  cnf(c_0_59, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r5_binop_1(X1,X3,X4)|~r6_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X5),k6_filter_1(X1,X2,X4,X6))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X6)|~v1_funct_1(X5)|~v1_funct_1(X4)|~v1_funct_1(X3)), inference(spm,[status(thm)],[c_0_52, c_0_44])).
% 0.18/0.46  cnf(c_0_60, negated_conjecture, (r4_binop_1(esk1_0,esk3_0,esk4_0)|~r6_binop_1(esk2_0,X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))|~v1_funct_2(X1,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)|~v1_funct_1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.18/0.46  cnf(c_0_61, negated_conjecture, (r6_binop_1(esk2_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_29]), c_0_31]), c_0_33])]), c_0_57])).
% 0.18/0.46  cnf(c_0_62, negated_conjecture, (v1_xboole_0(X1)|r5_binop_1(k2_zfmisc_1(X1,esk2_0),k6_filter_1(X1,esk2_0,X2,X3),k6_filter_1(X1,esk2_0,X4,esk6_0))|~r5_binop_1(esk2_0,X3,esk6_0)|~r5_binop_1(X1,X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)|~v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X4)|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_28]), c_0_30]), c_0_32])]), c_0_34])).
% 0.18/0.46  cnf(c_0_63, negated_conjecture, (v1_xboole_0(X1)|r5_binop_1(k2_zfmisc_1(X1,esk1_0),k6_filter_1(X1,esk1_0,X2,esk3_0),k6_filter_1(X1,esk1_0,X3,esk4_0))|~r5_binop_1(esk1_0,esk3_0,esk4_0)|~r5_binop_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_23]), c_0_24]), c_0_25])])).
% 0.18/0.46  cnf(c_0_64, negated_conjecture, (r5_binop_1(esk1_0,X1,esk4_0)|~r6_binop_1(esk1_0,X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))|~v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_16]), c_0_17]), c_0_18])])).
% 0.18/0.46  cnf(c_0_65, negated_conjecture, (r6_binop_1(esk1_0,X1,esk4_0)|~r5_binop_1(esk1_0,X1,esk4_0)|~r4_binop_1(esk1_0,X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))|~v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_16]), c_0_17]), c_0_18])])).
% 0.18/0.46  cnf(c_0_66, negated_conjecture, (r5_binop_1(esk1_0,esk3_0,esk4_0)|r6_binop_1(esk1_0,esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_27]), c_0_28]), c_0_29]), c_0_16]), c_0_23]), c_0_30]), c_0_31]), c_0_17]), c_0_24]), c_0_32]), c_0_33]), c_0_18]), c_0_25])]), c_0_19]), c_0_34])).
% 0.18/0.46  cnf(c_0_67, negated_conjecture, (r4_binop_1(esk1_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_29]), c_0_61]), c_0_31]), c_0_33])])).
% 0.18/0.46  cnf(c_0_68, negated_conjecture, (v1_xboole_0(X1)|r5_binop_1(k2_zfmisc_1(X1,esk2_0),k6_filter_1(X1,esk2_0,X2,esk5_0),k6_filter_1(X1,esk2_0,X3,esk6_0))|~r5_binop_1(esk2_0,esk5_0,esk6_0)|~r5_binop_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_29]), c_0_31]), c_0_33])])).
% 0.18/0.46  cnf(c_0_69, negated_conjecture, (r5_binop_1(esk2_0,X1,esk6_0)|~r6_binop_1(esk2_0,X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))|~v1_funct_2(X1,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_28]), c_0_30]), c_0_32])])).
% 0.18/0.46  cnf(c_0_70, negated_conjecture, (v1_xboole_0(X1)|r4_binop_1(k2_zfmisc_1(X1,esk2_0),k6_filter_1(X1,esk2_0,X2,X3),k6_filter_1(X1,esk2_0,X4,esk6_0))|~r4_binop_1(esk2_0,X3,esk6_0)|~r4_binop_1(X1,X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)|~v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X4)|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_28]), c_0_30]), c_0_32])]), c_0_34])).
% 0.18/0.46  cnf(c_0_71, negated_conjecture, (v1_xboole_0(X1)|r5_binop_1(k2_zfmisc_1(X1,esk1_0),k6_filter_1(X1,esk1_0,X2,esk3_0),k6_filter_1(X1,esk1_0,X3,esk4_0))|~r5_binop_1(X1,X2,X3)|~r6_binop_1(esk1_0,esk3_0,esk4_0)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_23]), c_0_24]), c_0_25])])).
% 0.18/0.46  cnf(c_0_72, negated_conjecture, (r6_binop_1(esk1_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_23]), c_0_24]), c_0_25])])).
% 0.18/0.46  cnf(c_0_73, negated_conjecture, (v1_xboole_0(X1)|r5_binop_1(k2_zfmisc_1(X1,esk2_0),k6_filter_1(X1,esk2_0,X2,esk5_0),k6_filter_1(X1,esk2_0,X3,esk6_0))|~r5_binop_1(X1,X2,X3)|~r6_binop_1(esk2_0,esk5_0,esk6_0)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_29]), c_0_31]), c_0_33])])).
% 0.18/0.46  cnf(c_0_74, negated_conjecture, (v1_xboole_0(X1)|r4_binop_1(k2_zfmisc_1(X1,esk2_0),k6_filter_1(X1,esk2_0,X2,esk5_0),k6_filter_1(X1,esk2_0,X3,esk6_0))|~r4_binop_1(esk2_0,esk5_0,esk6_0)|~r4_binop_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_29]), c_0_31]), c_0_33])])).
% 0.18/0.46  cnf(c_0_75, negated_conjecture, (v1_xboole_0(X1)|r5_binop_1(k2_zfmisc_1(X1,esk1_0),k6_filter_1(X1,esk1_0,X2,esk3_0),k6_filter_1(X1,esk1_0,X3,esk4_0))|~r5_binop_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72])])).
% 0.18/0.46  cnf(c_0_76, plain, (r6_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))|~r5_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))|~r4_binop_1(k2_zfmisc_1(X1,X2),X3,k6_filter_1(X1,X2,X4,X5))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))|~v1_funct_2(X5,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X5)|~v1_funct_1(X4)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_9]), c_0_10]), c_0_11])).
% 0.18/0.46  cnf(c_0_77, negated_conjecture, (v1_xboole_0(X1)|r5_binop_1(k2_zfmisc_1(X1,esk2_0),k6_filter_1(X1,esk2_0,X2,esk5_0),k6_filter_1(X1,esk2_0,X3,esk6_0))|~r5_binop_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_61])])).
% 0.18/0.46  cnf(c_0_78, negated_conjecture, (v1_xboole_0(X1)|r4_binop_1(k2_zfmisc_1(X1,esk2_0),k6_filter_1(X1,esk2_0,X2,esk5_0),k6_filter_1(X1,esk2_0,X3,esk6_0))|~r4_binop_1(X1,X2,X3)|~r6_binop_1(esk2_0,esk5_0,esk6_0)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_54]), c_0_29]), c_0_31]), c_0_33])])).
% 0.18/0.46  cnf(c_0_79, negated_conjecture, (r5_binop_1(k2_zfmisc_1(esk2_0,esk1_0),k6_filter_1(esk2_0,esk1_0,X1,esk3_0),k6_filter_1(esk2_0,esk1_0,esk6_0,esk4_0))|~r5_binop_1(esk2_0,X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))|~v1_funct_2(X1,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)|~v1_funct_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_28]), c_0_30]), c_0_32])]), c_0_34])).
% 0.18/0.46  cnf(c_0_80, negated_conjecture, (~r6_binop_1(esk1_0,esk3_0,esk4_0)|~r6_binop_1(esk2_0,esk5_0,esk6_0)|~r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.46  cnf(c_0_81, plain, (r6_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6))|~r5_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6))|~r4_binop_1(k2_zfmisc_1(X1,X2),k6_filter_1(X1,X2,X3,X4),k6_filter_1(X1,X2,X5,X6))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X6,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X6)|~v1_funct_1(X5)|~v1_funct_1(X4)|~v1_funct_1(X3)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_9]), c_0_10]), c_0_11])).
% 0.18/0.46  cnf(c_0_82, negated_conjecture, (r5_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,X1,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))|~r5_binop_1(esk1_0,X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))|~v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)|~v1_funct_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.18/0.46  cnf(c_0_83, negated_conjecture, (v1_xboole_0(X1)|r4_binop_1(k2_zfmisc_1(X1,esk2_0),k6_filter_1(X1,esk2_0,X2,esk5_0),k6_filter_1(X1,esk2_0,X3,esk6_0))|~r4_binop_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~v1_funct_1(X3)|~v1_funct_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_57]), c_0_78])).
% 0.18/0.46  cnf(c_0_84, negated_conjecture, (r5_binop_1(esk1_0,esk3_0,esk4_0)|~r5_binop_1(esk2_0,X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))|~v1_funct_2(X1,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)|~v1_funct_1(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_79]), c_0_28]), c_0_16]), c_0_23]), c_0_30]), c_0_17]), c_0_24]), c_0_32]), c_0_18]), c_0_25])]), c_0_34]), c_0_19])).
% 0.18/0.46  cnf(c_0_85, negated_conjecture, (~r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))|~r6_binop_1(esk1_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_61])])).
% 0.18/0.46  cnf(c_0_86, negated_conjecture, (r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,X1,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))|~r5_binop_1(esk1_0,X1,esk4_0)|~r4_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,X1,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))|~v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_28]), c_0_16]), c_0_29]), c_0_30]), c_0_17]), c_0_31]), c_0_32]), c_0_18]), c_0_33])])).
% 0.18/0.46  cnf(c_0_87, negated_conjecture, (r4_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,X1,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))|~r4_binop_1(esk1_0,X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))|~v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)|~v1_funct_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.18/0.46  cnf(c_0_88, negated_conjecture, (r5_binop_1(esk1_0,esk3_0,esk4_0)|~r6_binop_1(esk2_0,X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)))|~v1_funct_2(X1,k2_zfmisc_1(esk2_0,esk2_0),esk2_0)|~v1_funct_1(X1)), inference(spm,[status(thm)],[c_0_84, c_0_69])).
% 0.18/0.46  cnf(c_0_89, negated_conjecture, (~r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,esk3_0,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_72])])).
% 0.18/0.46  cnf(c_0_90, negated_conjecture, (r6_binop_1(k2_zfmisc_1(esk1_0,esk2_0),k6_filter_1(esk1_0,esk2_0,X1,esk5_0),k6_filter_1(esk1_0,esk2_0,esk4_0,esk6_0))|~r5_binop_1(esk1_0,X1,esk4_0)|~r4_binop_1(esk1_0,X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))|~v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)|~v1_funct_1(X1)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.18/0.46  cnf(c_0_91, negated_conjecture, (r5_binop_1(esk1_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_29]), c_0_61]), c_0_31]), c_0_33])])).
% 0.18/0.46  cnf(c_0_92, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91]), c_0_67]), c_0_23]), c_0_24]), c_0_25])]), ['proof']).
% 0.18/0.46  # SZS output end CNFRefutation
% 0.18/0.46  # Proof object total steps             : 93
% 0.18/0.46  # Proof object clause steps            : 82
% 0.18/0.46  # Proof object formula steps           : 11
% 0.18/0.46  # Proof object conjectures             : 63
% 0.18/0.46  # Proof object clause conjectures      : 60
% 0.18/0.46  # Proof object formula conjectures     : 3
% 0.18/0.46  # Proof object initial clauses used    : 29
% 0.18/0.46  # Proof object initial formulas used   : 5
% 0.18/0.46  # Proof object generating inferences   : 49
% 0.18/0.46  # Proof object simplifying inferences  : 218
% 0.18/0.46  # Training examples: 0 positive, 0 negative
% 0.18/0.46  # Parsed axioms                        : 5
% 0.18/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.46  # Initial clauses                      : 29
% 0.18/0.46  # Removed in clause preprocessing      : 0
% 0.18/0.46  # Initial clauses in saturation        : 29
% 0.18/0.46  # Processed clauses                    : 701
% 0.18/0.46  # ...of these trivial                  : 1
% 0.18/0.46  # ...subsumed                          : 6
% 0.18/0.46  # ...remaining for further processing  : 694
% 0.18/0.46  # Other redundant clauses eliminated   : 0
% 0.18/0.46  # Clauses deleted for lack of memory   : 0
% 0.18/0.46  # Backward-subsumed                    : 37
% 0.18/0.46  # Backward-rewritten                   : 47
% 0.18/0.46  # Generated clauses                    : 834
% 0.18/0.46  # ...of the previous two non-trivial   : 775
% 0.18/0.46  # Contextual simplify-reflections      : 103
% 0.18/0.46  # Paramodulations                      : 834
% 0.18/0.46  # Factorizations                       : 0
% 0.18/0.46  # Equation resolutions                 : 0
% 0.18/0.46  # Propositional unsat checks           : 0
% 0.18/0.46  #    Propositional check models        : 0
% 0.18/0.46  #    Propositional check unsatisfiable : 0
% 0.18/0.46  #    Propositional clauses             : 0
% 0.18/0.46  #    Propositional clauses after purity: 0
% 0.18/0.46  #    Propositional unsat core size     : 0
% 0.18/0.46  #    Propositional preprocessing time  : 0.000
% 0.18/0.46  #    Propositional encoding time       : 0.000
% 0.18/0.46  #    Propositional solver time         : 0.000
% 0.18/0.46  #    Success case prop preproc time    : 0.000
% 0.18/0.46  #    Success case prop encoding time   : 0.000
% 0.18/0.46  #    Success case prop solver time     : 0.000
% 0.18/0.46  # Current number of processed clauses  : 581
% 0.18/0.46  #    Positive orientable unit clauses  : 334
% 0.18/0.46  #    Positive unorientable unit clauses: 0
% 0.18/0.46  #    Negative unit clauses             : 3
% 0.18/0.46  #    Non-unit-clauses                  : 244
% 0.18/0.46  # Current number of unprocessed clauses: 130
% 0.18/0.46  # ...number of literals in the above   : 1329
% 0.18/0.46  # Current number of archived formulas  : 0
% 0.18/0.46  # Current number of archived clauses   : 113
% 0.18/0.46  # Clause-clause subsumption calls (NU) : 16346
% 0.18/0.46  # Rec. Clause-clause subsumption calls : 1891
% 0.18/0.46  # Non-unit clause-clause subsumptions  : 120
% 0.18/0.46  # Unit Clause-clause subsumption calls : 961
% 0.18/0.46  # Rewrite failures with RHS unbound    : 0
% 0.18/0.46  # BW rewrite match attempts            : 22923
% 0.18/0.46  # BW rewrite match successes           : 6
% 0.18/0.46  # Condensation attempts                : 0
% 0.18/0.46  # Condensation successes               : 0
% 0.18/0.46  # Termbank termtop insertions          : 52571
% 0.18/0.46  
% 0.18/0.46  # -------------------------------------------------
% 0.18/0.46  # User time                : 0.116 s
% 0.18/0.46  # System time              : 0.009 s
% 0.18/0.46  # Total time               : 0.125 s
% 0.18/0.46  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
