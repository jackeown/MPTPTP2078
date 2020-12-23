%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1435+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:41 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 473 expanded)
%              Number of clauses        :  103 ( 121 expanded)
%              Number of leaves         :   11 ( 140 expanded)
%              Depth                    :   11
%              Number of atoms          : 1534 (7678 expanded)
%              Number of equality atoms :  236 ( 236 expanded)
%              Maximal formula depth    :   23 (   9 average)
%              Maximal clause size      :   40 (   8 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                    & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                        & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r5_binop_1(X1,X4,X5)
                              & r5_binop_1(X0,X2,X3) )
                          <=> r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r5_binop_1(X1,X4,X5)
                              & r5_binop_1(X0,X2,X3) )
                          <=> r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r5_binop_1(X1,X4,X5)
                              & r5_binop_1(X0,X2,X3) )
                          <=> r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r5_binop_1(X1,X4,X5)
                                & r5_binop_1(X0,X2,X3) )
                              | ~ r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                            & ( r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                              | ~ r5_binop_1(X1,X4,X5)
                              | ~ r5_binop_1(X0,X2,X3) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r5_binop_1(X1,X4,X5)
                                & r5_binop_1(X0,X2,X3) )
                              | ~ r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                            & ( r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                              | ~ r5_binop_1(X1,X4,X5)
                              | ~ r5_binop_1(X0,X2,X3) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | ~ r5_binop_1(X1,X4,X5)
      | ~ r5_binop_1(X0,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                    & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                        & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r4_binop_1(X1,X4,X5)
                              & r4_binop_1(X0,X2,X3) )
                          <=> r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r4_binop_1(X1,X4,X5)
                              & r4_binop_1(X0,X2,X3) )
                          <=> r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r4_binop_1(X1,X4,X5)
                              & r4_binop_1(X0,X2,X3) )
                          <=> r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r4_binop_1(X1,X4,X5)
                                & r4_binop_1(X0,X2,X3) )
                              | ~ r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                            & ( r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                              | ~ r4_binop_1(X1,X4,X5)
                              | ~ r4_binop_1(X0,X2,X3) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r4_binop_1(X1,X4,X5)
                                & r4_binop_1(X0,X2,X3) )
                              | ~ r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                            & ( r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                              | ~ r4_binop_1(X1,X4,X5)
                              | ~ r4_binop_1(X0,X2,X3) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | ~ r4_binop_1(X1,X4,X5)
      | ~ r4_binop_1(X0,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
         => ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r6_binop_1(X0,X1,X2)
              | ~ r5_binop_1(X0,X1,X2)
              | ~ r4_binop_1(X0,X1,X2) )
            & ( ( r5_binop_1(X0,X1,X2)
                & r4_binop_1(X0,X1,X2) )
              | ~ r6_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r6_binop_1(X0,X1,X2)
              | ~ r5_binop_1(X0,X1,X2)
              | ~ r4_binop_1(X0,X1,X2) )
            & ( ( r5_binop_1(X0,X1,X2)
                & r4_binop_1(X0,X1,X2) )
              | ~ r6_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r5_binop_1(X0,X1,X2)
      | ~ r6_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r4_binop_1(X0,X1,X2)
      | ~ r6_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k6_filter_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r6_binop_1(X0,X1,X2)
      | ~ r5_binop_1(X0,X1,X2)
      | ~ r4_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r5_binop_1(X1,X4,X5)
      | ~ r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r5_binop_1(X0,X2,X3)
      | ~ r5_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r4_binop_1(X1,X4,X5)
      | ~ r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r4_binop_1(X0,X2,X3)
      | ~ r4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                    & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                        & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r6_binop_1(X1,X4,X5)
                              & r6_binop_1(X0,X2,X3) )
                          <=> r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                              & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                              & v1_funct_1(X5) )
                           => ( ( r6_binop_1(X1,X4,X5)
                                & r6_binop_1(X0,X2,X3) )
                            <=> r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( r6_binop_1(X1,X4,X5)
                              & r6_binop_1(X0,X2,X3) )
                          <~> r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( r6_binop_1(X1,X4,X5)
                              & r6_binop_1(X0,X2,X3) )
                          <~> r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                            | ~ r6_binop_1(X1,X4,X5)
                            | ~ r6_binop_1(X0,X2,X3) )
                          & ( r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                            | ( r6_binop_1(X1,X4,X5)
                              & r6_binop_1(X0,X2,X3) ) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                            | ~ r6_binop_1(X1,X4,X5)
                            | ~ r6_binop_1(X0,X2,X3) )
                          & ( r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                            | ( r6_binop_1(X1,X4,X5)
                              & r6_binop_1(X0,X2,X3) ) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
            | ~ r6_binop_1(X1,X4,X5)
            | ~ r6_binop_1(X0,X2,X3) )
          & ( r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
            | ( r6_binop_1(X1,X4,X5)
              & r6_binop_1(X0,X2,X3) ) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
          & v1_funct_1(X5) )
     => ( ( ~ r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,sK5))
          | ~ r6_binop_1(X1,X4,sK5)
          | ~ r6_binop_1(X0,X2,X3) )
        & ( r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,sK5))
          | ( r6_binop_1(X1,X4,sK5)
            & r6_binop_1(X0,X2,X3) ) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        & v1_funct_2(sK5,k2_zfmisc_1(X1,X1),X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                | ~ r6_binop_1(X1,X4,X5)
                | ~ r6_binop_1(X0,X2,X3) )
              & ( r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                | ( r6_binop_1(X1,X4,X5)
                  & r6_binop_1(X0,X2,X3) ) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
              & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
          & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ( ~ r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,sK4),k6_filter_1(X0,X1,X3,X5))
              | ~ r6_binop_1(X1,sK4,X5)
              | ~ r6_binop_1(X0,X2,X3) )
            & ( r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,sK4),k6_filter_1(X0,X1,X3,X5))
              | ( r6_binop_1(X1,sK4,X5)
                & r6_binop_1(X0,X2,X3) ) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
            & v1_funct_1(X5) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        & v1_funct_2(sK4,k2_zfmisc_1(X1,X1),X1)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                    | ~ r6_binop_1(X1,X4,X5)
                    | ~ r6_binop_1(X0,X2,X3) )
                  & ( r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                    | ( r6_binop_1(X1,X4,X5)
                      & r6_binop_1(X0,X2,X3) ) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                  & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
              & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,sK3,X5))
                  | ~ r6_binop_1(X1,X4,X5)
                  | ~ r6_binop_1(X0,X2,sK3) )
                & ( r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,sK3,X5))
                  | ( r6_binop_1(X1,X4,X5)
                    & r6_binop_1(X0,X2,sK3) ) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
            & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(sK3,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                        | ~ r6_binop_1(X1,X4,X5)
                        | ~ r6_binop_1(X0,X2,X3) )
                      & ( r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                        | ( r6_binop_1(X1,X4,X5)
                          & r6_binop_1(X0,X2,X3) ) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                  & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,sK2,X4),k6_filter_1(X0,X1,X3,X5))
                      | ~ r6_binop_1(X1,X4,X5)
                      | ~ r6_binop_1(X0,sK2,X3) )
                    & ( r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,sK2,X4),k6_filter_1(X0,X1,X3,X5))
                      | ( r6_binop_1(X1,X4,X5)
                        & r6_binop_1(X0,sK2,X3) ) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                    & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X3) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(sK2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                            | ~ r6_binop_1(X1,X4,X5)
                            | ~ r6_binop_1(X0,X2,X3) )
                          & ( r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                            | ( r6_binop_1(X1,X4,X5)
                              & r6_binop_1(X0,X2,X3) ) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ r6_binop_1(k2_zfmisc_1(X0,sK1),k6_filter_1(X0,sK1,X2,X4),k6_filter_1(X0,sK1,X3,X5))
                          | ~ r6_binop_1(sK1,X4,X5)
                          | ~ r6_binop_1(X0,X2,X3) )
                        & ( r6_binop_1(k2_zfmisc_1(X0,sK1),k6_filter_1(X0,sK1,X2,X4),k6_filter_1(X0,sK1,X3,X5))
                          | ( r6_binop_1(sK1,X4,X5)
                            & r6_binop_1(X0,X2,X3) ) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
                        & v1_funct_2(X5,k2_zfmisc_1(sK1,sK1),sK1)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
                    & v1_funct_2(X4,k2_zfmisc_1(sK1,sK1),sK1)
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                              | ~ r6_binop_1(X1,X4,X5)
                              | ~ r6_binop_1(X0,X2,X3) )
                            & ( r6_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                              | ( r6_binop_1(X1,X4,X5)
                                & r6_binop_1(X0,X2,X3) ) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                        & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                    & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r6_binop_1(k2_zfmisc_1(sK0,X1),k6_filter_1(sK0,X1,X2,X4),k6_filter_1(sK0,X1,X3,X5))
                            | ~ r6_binop_1(X1,X4,X5)
                            | ~ r6_binop_1(sK0,X2,X3) )
                          & ( r6_binop_1(k2_zfmisc_1(sK0,X1),k6_filter_1(sK0,X1,X2,X4),k6_filter_1(sK0,X1,X3,X5))
                            | ( r6_binop_1(X1,X4,X5)
                              & r6_binop_1(sK0,X2,X3) ) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
                  & v1_funct_2(X3,k2_zfmisc_1(sK0,sK0),sK0)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
              & v1_funct_2(X2,k2_zfmisc_1(sK0,sK0),sK0)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
      | ~ r6_binop_1(sK1,sK4,sK5)
      | ~ r6_binop_1(sK0,sK2,sK3) )
    & ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
      | ( r6_binop_1(sK1,sK4,sK5)
        & r6_binop_1(sK0,sK2,sK3) ) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    & v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    & v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    & v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    & v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f24,f30,f29,f28,f27,f26,f25])).

fof(f60,plain,
    ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ r6_binop_1(sK1,sK4,sK5)
    | ~ r6_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,
    ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | r6_binop_1(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,
    ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | r6_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X3,X3),X3)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
    | ~ r5_binop_1(X3,X4,X2)
    | ~ r5_binop_1(X1,X0,X5)
    | r5_binop_1(k2_zfmisc_1(X1,X3),k6_filter_1(X1,X3,X0,X4),k6_filter_1(X1,X3,X5,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_300,plain,
    ( ~ v1_funct_2(X0_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ v1_funct_2(X1_45,k2_zfmisc_1(X1_44,X1_44),X1_44)
    | ~ v1_funct_2(X2_45,k2_zfmisc_1(X1_44,X1_44),X1_44)
    | ~ v1_funct_2(X3_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ r5_binop_1(X1_44,X2_45,X1_45)
    | ~ r5_binop_1(X0_44,X0_45,X3_45)
    | r5_binop_1(k2_zfmisc_1(X0_44,X1_44),k6_filter_1(X0_44,X1_44,X0_45,X2_45),k6_filter_1(X0_44,X1_44,X3_45,X1_45))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_44,X1_44),X1_44)))
    | ~ m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_44,X1_44),X1_44)))
    | ~ m1_subset_1(X3_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | v1_xboole_0(X1_44)
    | v1_xboole_0(X0_44)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X2_45)
    | ~ v1_funct_1(X3_45)
    | ~ v1_funct_1(X1_45) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_497,plain,
    ( ~ v1_funct_2(X0_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ v1_funct_2(X1_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ r5_binop_1(X0_44,X0_45,X1_45)
    | r5_binop_1(k2_zfmisc_1(X0_44,sK1),k6_filter_1(X0_44,sK1,X0_45,sK4),k6_filter_1(X0_44,sK1,X1_45,sK5))
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | v1_xboole_0(X0_44)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X1_45)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_658,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ r5_binop_1(sK1,sK4,sK5)
    | ~ r5_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_659,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) = iProver_top
    | r5_binop_1(sK1,sK4,sK5) != iProver_top
    | r5_binop_1(sK0,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X3,X3),X3)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
    | ~ r4_binop_1(X3,X4,X2)
    | ~ r4_binop_1(X1,X0,X5)
    | r4_binop_1(k2_zfmisc_1(X1,X3),k6_filter_1(X1,X3,X0,X4),k6_filter_1(X1,X3,X5,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_303,plain,
    ( ~ v1_funct_2(X0_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ v1_funct_2(X1_45,k2_zfmisc_1(X1_44,X1_44),X1_44)
    | ~ v1_funct_2(X2_45,k2_zfmisc_1(X1_44,X1_44),X1_44)
    | ~ v1_funct_2(X3_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ r4_binop_1(X1_44,X2_45,X1_45)
    | ~ r4_binop_1(X0_44,X0_45,X3_45)
    | r4_binop_1(k2_zfmisc_1(X0_44,X1_44),k6_filter_1(X0_44,X1_44,X0_45,X2_45),k6_filter_1(X0_44,X1_44,X3_45,X1_45))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_44,X1_44),X1_44)))
    | ~ m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_44,X1_44),X1_44)))
    | ~ m1_subset_1(X3_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | v1_xboole_0(X1_44)
    | v1_xboole_0(X0_44)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X2_45)
    | ~ v1_funct_1(X3_45)
    | ~ v1_funct_1(X1_45) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_479,plain,
    ( ~ v1_funct_2(X0_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ v1_funct_2(X1_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ r4_binop_1(X0_44,X0_45,X1_45)
    | r4_binop_1(k2_zfmisc_1(X0_44,sK1),k6_filter_1(X0_44,sK1,X0_45,sK4),k6_filter_1(X0_44,sK1,X1_45,sK5))
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | v1_xboole_0(X0_44)
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X1_45)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_561,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_562,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) = iProver_top
    | r4_binop_1(sK1,sK4,sK5) != iProver_top
    | r4_binop_1(sK0,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | r5_binop_1(X1,X2,X0)
    | ~ r6_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_310,plain,
    ( ~ v1_funct_2(X0_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ v1_funct_2(X1_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | r5_binop_1(X0_44,X1_45,X0_45)
    | ~ r6_binop_1(X0_44,X1_45,X0_45)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X1_45) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_541,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | r5_binop_1(sK1,sK4,sK5)
    | ~ r6_binop_1(sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_545,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | r5_binop_1(sK1,sK4,sK5) = iProver_top
    | r6_binop_1(sK1,sK4,sK5) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | r4_binop_1(X1,X2,X0)
    | ~ r6_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_309,plain,
    ( ~ v1_funct_2(X0_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ v1_funct_2(X1_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | r4_binop_1(X0_44,X1_45,X0_45)
    | ~ r6_binop_1(X0_44,X1_45,X0_45)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X1_45) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_542,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | r4_binop_1(sK1,sK4,sK5)
    | ~ r6_binop_1(sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_543,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | r4_binop_1(sK1,sK4,sK5) = iProver_top
    | r6_binop_1(sK1,sK4,sK5) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_535,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | r5_binop_1(sK0,sK2,sK3)
    | ~ r6_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_539,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r5_binop_1(sK0,sK2,sK3) = iProver_top
    | r6_binop_1(sK0,sK2,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_536,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | r4_binop_1(sK0,sK2,sK3)
    | ~ r6_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_537,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r4_binop_1(sK0,sK2,sK3) = iProver_top
    | r6_binop_1(sK0,sK2,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | m1_subset_1(k6_filter_1(X1,X3,X0,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3)),k2_zfmisc_1(X1,X3))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_308,plain,
    ( ~ v1_funct_2(X0_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ v1_funct_2(X1_45,k2_zfmisc_1(X1_44,X1_44),X1_44)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_44,X1_44),X1_44)))
    | m1_subset_1(k6_filter_1(X0_44,X1_44,X0_45,X1_45),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X1_44),k2_zfmisc_1(X0_44,X1_44)),k2_zfmisc_1(X0_44,X1_44))))
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X1_45) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_527,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_308])).

cnf(c_528,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_527])).

cnf(c_523,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_308])).

cnf(c_524,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
    | v1_funct_2(k6_filter_1(X1,X3,X0,X2),k2_zfmisc_1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3)),k2_zfmisc_1(X1,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_307,plain,
    ( ~ v1_funct_2(X0_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ v1_funct_2(X1_45,k2_zfmisc_1(X1_44,X1_44),X1_44)
    | v1_funct_2(k6_filter_1(X0_44,X1_44,X0_45,X1_45),k2_zfmisc_1(k2_zfmisc_1(X0_44,X1_44),k2_zfmisc_1(X0_44,X1_44)),k2_zfmisc_1(X0_44,X1_44))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_44,X1_44),X1_44)))
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X1_45) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_519,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_307])).

cnf(c_520,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) = iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_515,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_307])).

cnf(c_516,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) = iProver_top
    | v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | v1_funct_1(k6_filter_1(X1,X3,X0,X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_306,plain,
    ( ~ v1_funct_2(X0_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ v1_funct_2(X1_45,k2_zfmisc_1(X1_44,X1_44),X1_44)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_44,X1_44),X1_44)))
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X1_45)
    | v1_funct_1(k6_filter_1(X0_44,X1_44,X0_45,X1_45)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_511,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_512,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_507,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_508,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ r4_binop_1(X1,X2,X0)
    | ~ r5_binop_1(X1,X2,X0)
    | r6_binop_1(X1,X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_311,plain,
    ( ~ v1_funct_2(X0_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ v1_funct_2(X1_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ r4_binop_1(X0_44,X1_45,X0_45)
    | ~ r5_binop_1(X0_44,X1_45,X0_45)
    | r6_binop_1(X0_44,X1_45,X0_45)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X1_45) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_492,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ r4_binop_1(sK0,sK2,sK3)
    | ~ r5_binop_1(sK0,sK2,sK3)
    | r6_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_493,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r4_binop_1(sK0,sK2,sK3) != iProver_top
    | r5_binop_1(sK0,sK2,sK3) != iProver_top
    | r6_binop_1(sK0,sK2,sK3) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_484,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ r4_binop_1(sK1,sK4,sK5)
    | ~ r5_binop_1(sK1,sK4,sK5)
    | r6_binop_1(sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_485,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | r4_binop_1(sK1,sK4,sK5) != iProver_top
    | r5_binop_1(sK1,sK4,sK5) != iProver_top
    | r6_binop_1(sK1,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X3,X3),X3)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
    | r5_binop_1(X3,X4,X2)
    | ~ r5_binop_1(k2_zfmisc_1(X1,X3),k6_filter_1(X1,X3,X0,X4),k6_filter_1(X1,X3,X5,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_302,plain,
    ( ~ v1_funct_2(X0_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ v1_funct_2(X1_45,k2_zfmisc_1(X1_44,X1_44),X1_44)
    | ~ v1_funct_2(X2_45,k2_zfmisc_1(X1_44,X1_44),X1_44)
    | ~ v1_funct_2(X3_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | r5_binop_1(X1_44,X2_45,X1_45)
    | ~ r5_binop_1(k2_zfmisc_1(X0_44,X1_44),k6_filter_1(X0_44,X1_44,X0_45,X2_45),k6_filter_1(X0_44,X1_44,X3_45,X1_45))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_44,X1_44),X1_44)))
    | ~ m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_44,X1_44),X1_44)))
    | ~ m1_subset_1(X3_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | v1_xboole_0(X1_44)
    | v1_xboole_0(X0_44)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X2_45)
    | ~ v1_funct_1(X3_45)
    | ~ v1_funct_1(X1_45) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_473,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | r5_binop_1(sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_477,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) != iProver_top
    | r5_binop_1(sK1,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X3,X3),X3)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
    | r5_binop_1(X1,X0,X5)
    | ~ r5_binop_1(k2_zfmisc_1(X1,X3),k6_filter_1(X1,X3,X0,X4),k6_filter_1(X1,X3,X5,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_301,plain,
    ( ~ v1_funct_2(X0_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ v1_funct_2(X1_45,k2_zfmisc_1(X1_44,X1_44),X1_44)
    | ~ v1_funct_2(X2_45,k2_zfmisc_1(X1_44,X1_44),X1_44)
    | ~ v1_funct_2(X3_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | r5_binop_1(X0_44,X0_45,X3_45)
    | ~ r5_binop_1(k2_zfmisc_1(X0_44,X1_44),k6_filter_1(X0_44,X1_44,X0_45,X2_45),k6_filter_1(X0_44,X1_44,X3_45,X1_45))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_44,X1_44),X1_44)))
    | ~ m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_44,X1_44),X1_44)))
    | ~ m1_subset_1(X3_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | v1_xboole_0(X1_44)
    | v1_xboole_0(X0_44)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X2_45)
    | ~ v1_funct_1(X3_45)
    | ~ v1_funct_1(X1_45) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_474,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | r5_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_475,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) != iProver_top
    | r5_binop_1(sK0,sK2,sK3) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_465,plain,
    ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_466,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) != iProver_top
    | r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) != iProver_top
    | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) != iProver_top
    | r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) = iProver_top
    | m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) != iProver_top
    | m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) != iProver_top
    | v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5)) != iProver_top
    | v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X3,X3),X3)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
    | r4_binop_1(X3,X4,X2)
    | ~ r4_binop_1(k2_zfmisc_1(X1,X3),k6_filter_1(X1,X3,X0,X4),k6_filter_1(X1,X3,X5,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_305,plain,
    ( ~ v1_funct_2(X0_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ v1_funct_2(X1_45,k2_zfmisc_1(X1_44,X1_44),X1_44)
    | ~ v1_funct_2(X2_45,k2_zfmisc_1(X1_44,X1_44),X1_44)
    | ~ v1_funct_2(X3_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | r4_binop_1(X1_44,X2_45,X1_45)
    | ~ r4_binop_1(k2_zfmisc_1(X0_44,X1_44),k6_filter_1(X0_44,X1_44,X0_45,X2_45),k6_filter_1(X0_44,X1_44,X3_45,X1_45))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_44,X1_44),X1_44)))
    | ~ m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_44,X1_44),X1_44)))
    | ~ m1_subset_1(X3_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | v1_xboole_0(X1_44)
    | v1_xboole_0(X0_44)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X2_45)
    | ~ v1_funct_1(X3_45)
    | ~ v1_funct_1(X1_45) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_459,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | r4_binop_1(sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_305])).

cnf(c_463,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) != iProver_top
    | r4_binop_1(sK1,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X3,X3),X3)
    | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
    | r4_binop_1(X1,X0,X5)
    | ~ r4_binop_1(k2_zfmisc_1(X1,X3),k6_filter_1(X1,X3,X0,X4),k6_filter_1(X1,X3,X5,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_304,plain,
    ( ~ v1_funct_2(X0_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | ~ v1_funct_2(X1_45,k2_zfmisc_1(X1_44,X1_44),X1_44)
    | ~ v1_funct_2(X2_45,k2_zfmisc_1(X1_44,X1_44),X1_44)
    | ~ v1_funct_2(X3_45,k2_zfmisc_1(X0_44,X0_44),X0_44)
    | r4_binop_1(X0_44,X0_45,X3_45)
    | ~ r4_binop_1(k2_zfmisc_1(X0_44,X1_44),k6_filter_1(X0_44,X1_44,X0_45,X2_45),k6_filter_1(X0_44,X1_44,X3_45,X1_45))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_44,X1_44),X1_44)))
    | ~ m1_subset_1(X2_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1_44,X1_44),X1_44)))
    | ~ m1_subset_1(X3_45,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0_44,X0_44),X0_44)))
    | v1_xboole_0(X1_44)
    | v1_xboole_0(X0_44)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X2_45)
    | ~ v1_funct_1(X3_45)
    | ~ v1_funct_1(X1_45) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_460,plain,
    ( ~ v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | r4_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_304])).

cnf(c_461,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) != iProver_top
    | v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) != iProver_top
    | r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) != iProver_top
    | r4_binop_1(sK0,sK2,sK3) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_451,plain,
    ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_452,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) != iProver_top
    | r5_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) = iProver_top
    | r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) != iProver_top
    | m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) != iProver_top
    | m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) != iProver_top
    | v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5)) != iProver_top
    | v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_448,plain,
    ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_449,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_funct_2(k6_filter_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) != iProver_top
    | r4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) = iProver_top
    | r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) != iProver_top
    | m1_subset_1(k6_filter_1(sK0,sK1,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) != iProver_top
    | m1_subset_1(k6_filter_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) != iProver_top
    | v1_funct_1(k6_filter_1(sK0,sK1,sK3,sK5)) != iProver_top
    | v1_funct_1(k6_filter_1(sK0,sK1,sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_12,negated_conjecture,
    ( ~ r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | ~ r6_binop_1(sK1,sK4,sK5)
    | ~ r6_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_45,plain,
    ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) != iProver_top
    | r6_binop_1(sK1,sK4,sK5) != iProver_top
    | r6_binop_1(sK0,sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13,negated_conjecture,
    ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | r6_binop_1(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_44,plain,
    ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) = iProver_top
    | r6_binop_1(sK1,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,negated_conjecture,
    ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5))
    | r6_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_43,plain,
    ( r6_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK2,sK4),k6_filter_1(sK0,sK1,sK3,sK5)) = iProver_top
    | r6_binop_1(sK0,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_42,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_41,plain,
    ( v1_funct_2(sK5,k2_zfmisc_1(sK1,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_40,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_39,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_38,plain,
    ( v1_funct_2(sK4,k2_zfmisc_1(sK1,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_37,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_35,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_34,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_32,plain,
    ( v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_31,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_27,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_30,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_29,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_659,c_562,c_545,c_543,c_539,c_537,c_528,c_524,c_520,c_516,c_512,c_508,c_493,c_485,c_477,c_475,c_466,c_463,c_461,c_452,c_449,c_45,c_44,c_43,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_29])).


%------------------------------------------------------------------------------
